#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

Live_moveList Live_MoveList(Live_move head, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->head = head;
	lm->tail = tail;
	return lm;
}

Live_move Live_Move(G_node src, G_node dst) {
	Live_move m = (Live_move) checked_malloc(sizeof(*m));
	m->src = src;
	m->dst = dst;
	return m;
}

Temp_temp Live_gtemp(G_node n) {
	return (Temp_temp) G_nodeInfo(n);
}

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) {
	G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flowNode) {
	return (Temp_tempList)G_look(t, flowNode);
}

static Live_moveList lookupMoveMap(G_table t, G_node iNode) {
	return (Live_moveList)G_look(t, iNode);
}

static double lookupCostMap(G_table t, G_node iNode) {
	double *p = G_look(t, iNode);
	if (p) return *p;
	return 0.0;
}

static void enterCostMap(G_table t, G_node iNode, double d) {
	double* p = G_look(t, iNode);
	if (!p) {
		p = checked_malloc(sizeof(double));
		G_enter(t, iNode, p);
	}
	*p = d;
}

static void enterMoveMap(G_table t, G_node src, G_node dst) {
	G_enter(t, src, Live_MoveList(Live_Move(src, dst), lookupMoveMap(t, src)));
	G_enter(t, dst, Live_MoveList(Live_Move(src, dst), lookupMoveMap(t, dst)));
}

static Temp_tempList Join(Temp_tempList a, Temp_tempList b, bool *dirty) {
	Temp_tempList s = Temp_tempComplement(b, a);
	if (s) {
		if (dirty) {
			*dirty = TRUE;
		}
		return Temp_tempSplice(a, s);
	} else {
		return a;
	}
}

G_table buildLiveMap(G_graph flow) {
	G_table livein = G_empty();
	G_table liveout = G_empty();
	G_nodeList rnodes = G_rnodes(flow);

	bool dirty = FALSE;
	/* build up liveMap */
	do {
		dirty = FALSE;
		for (G_nodeList nl = rnodes; nl; nl=nl->tail) {
			G_node node = nl->head;

			Temp_tempList in = lookupLiveMap(livein, node);
			Temp_tempList out = lookupLiveMap(liveout, node);
			Temp_tempList use = FG_use(node);
			Temp_tempList def = FG_def(node);

			G_nodeList succ = G_succ(node);
			Temp_tempList new_out = NULL;
			for (; succ; succ=succ->tail) {
				G_node s_node = succ->head;
				Temp_tempList s_in = lookupLiveMap(livein, s_node);
				new_out = Temp_tempUnion(new_out, s_in);
			}
			out = Join(out, new_out, &dirty);

			in = Join(in, Temp_tempUnion(use, Temp_tempComplement(out, def)), &dirty);

			enterLiveMap(livein, node, in);
			enterLiveMap(liveout, node, out);
		}

	} while(dirty);
	return liveout;
}

struct Live_graph Live_liveness(G_graph flow) {
	G_nodeList nodes = G_nodes(flow);
	struct Live_graph lg;	

	G_graph g = G_Graph();
	Live_moveList ml = NULL;
	G_table temp_to_moves = G_empty();

	G_table liveout = buildLiveMap(flow);

	G_table cost = G_empty();
	
	/* build up interference graph*/
	/* add node */
	TAB_table temp_to_node = TAB_empty();
	Temp_tempList added_temps = NULL;
	for (G_nodeList nl = nodes; nl; nl=nl->tail) {
		G_node node = nl->head;
		Temp_tempList def = FG_def(node);
		Temp_tempList use = FG_use(node);
		Temp_tempList to_add = Temp_tempSplice(def, use);
		for (Temp_tempList tl = to_add; tl; tl=tl->tail) {
			Temp_temp t = tl->head;
			if (!Temp_tempIn(added_temps, t)) {
				TAB_enter(temp_to_node, t, G_Node(g, t));
				added_temps = Temp_TempList(t, added_temps);
			}
		}
	}
	/* add interference edge */
	for (G_nodeList nl = nodes; nl; nl=nl->tail) {
		G_node node = nl->head;
		Temp_tempList def = FG_def(node);
		Temp_tempList out = lookupLiveMap(liveout, node);
		Temp_tempList conflict = out;
		if (FG_isMove(node)) {
			Temp_tempList use = FG_use(node);
			G_node src = (G_node)TAB_look(temp_to_node, use->head);
			G_node dst = (G_node)TAB_look(temp_to_node, def->head);
			ml = Live_MoveList(Live_Move(src, dst), ml);
			enterMoveMap(temp_to_moves, src, dst);
			
			conflict = Temp_tempComplement(out, use);
		}

		for (Temp_tempList tl = def; tl; tl=tl->tail) {
			Temp_temp td = tl->head;
			for (Temp_tempList tll = conflict; tll; tll=tll->tail) {
				Temp_temp tc = tll->head;
				if (td == tc) continue;
				G_node td_node = (G_node)TAB_look(temp_to_node, td);
				G_node tc_node = (G_node)TAB_look(temp_to_node, tc);
				G_addEdge(td_node, tc_node);
				G_addEdge(tc_node, td_node);
				enterCostMap(cost, td_node, lookupCostMap(cost, td_node)+1);
				enterCostMap(cost, tc_node, lookupCostMap(cost, tc_node)+1);
			}
		}
	}
	/* set cost */
	G_nodeList nl = G_nodes(g);
	for (; nl; nl=nl->tail) {
		G_node n = nl->head;
		enterCostMap(cost, n, lookupCostMap(cost, n) / (G_degree(n) / 2));
	}

	lg.graph = g;
	lg.moves = ml;
	lg.temp_to_moves = temp_to_moves;
	lg.cost = cost;

	return lg;
}

//--------------set operation------------------------
bool Live_moveIn(Live_moveList ml, Live_move m) {
	for (; ml; ml=ml->tail) {
		if (ml->head->src == m->src && ml->head->dst == m->dst) {
			return TRUE;
		}
	}
	return FALSE;
}

Live_moveList Live_moveRemove(Live_moveList ml, Live_move m) {
	Live_moveList prev = NULL;
	Live_moveList origin = ml;
	for (; ml; ml=ml->tail) {
		if (ml->head->src == m->src && ml->head->dst == m->dst) {
			if (prev) {
				prev->tail = ml->tail;
				return origin;
			} else {
				return ml->tail;
			}
		}
		prev = ml;
	}
	return origin;
}

Live_moveList Live_moveComplement(Live_moveList in, Live_moveList notin) {
	Live_moveList res = NULL;
	for (; in; in=in->tail) {
		if (!Live_moveIn(notin, in->head)) {
			res = Live_MoveList(in->head, res);
		}
	}
	return res;
}

Live_moveList Live_moveSplice(Live_moveList a, Live_moveList b) {
  if (a==NULL) return b;
  return Live_MoveList(a->head, Live_moveSplice(a->tail, b));
}

Live_moveList Live_moveUnion(Live_moveList a, Live_moveList b) {
	Live_moveList s = Live_moveComplement(b, a);
	return Live_moveSplice(a, s);
}

Live_moveList Live_moveIntersect(Live_moveList a, Live_moveList b) {
	Live_moveList res = NULL;
	for (; a; a=a->tail) {
		if (Live_moveIn(b, a->head)) {
			res = Live_MoveList(a->head, res);
		}
	}
	return res;
}

Live_moveList Live_moveAppend(Live_moveList ml, Live_move m) {
	if (Live_moveIn(ml, m)) {
		return ml;
	} else {
		return Live_MoveList(m, ml);
	}
}