#include "prog1.h"
#include <stdio.h>
#include <string.h>

int maxargs(A_stm stm)
{
	if (stm->kind == A_compoundStm) {
		int l = maxargs(stm->u.compound.stm1);
		int r = maxargs(stm->u.compound.stm2);
		return l > r ? l : r;
	} else if (stm->kind == A_assignStm) {
		if (stm->u.assign.exp->kind == A_eseqExp) {
			return maxargs(stm->u.assign.exp->u.eseq.stm);
		} else {
			return 0;
		}
	} else { /* print statement */
		A_expList expList = stm->u.print.exps;
		int count = 1;
		A_expList next = expList;
		while (next->kind != A_lastExpList) {
			count ++;
			next = next->u.pair.tail;
		}
		next = expList;
		while (next->kind != A_lastExpList) {
			if (next->u.pair.head->kind == A_eseqExp) {
				int can = maxargs(next->u.pair.head->u.eseq.stm);
				count = can > count ? can : count;
			}
			next = next->u.pair.tail;
		}
		if (next->u.last->kind == A_eseqExp) {
			int can = maxargs(next->u.last->u.eseq.stm);
			count = can > count ? can : count;
		}
		return count;
	}
}

typedef struct table *Table_;
struct table {string id; int value; Table_ tail;};
Table_ Table(string id, int value, Table_ tail) 
{
	Table_ t = checked_malloc(sizeof(*t));
	t->id = id; t->value = value; t->tail = tail;
	return t;
}

int lookup(Table_ t, string key)
{
	Table_ next = t;
	while (next != NULL) {
		if (!strcmp(next->id, key)) {
			return next->value;
		}
		next = next->tail;
	}
}

Table_ interpStm(A_stm s, Table_ t);

typedef struct intAndTable {int i; Table_ t;} *IntAndTable_;
IntAndTable_ IntAndTable(int i, Table_ t)
{
	IntAndTable_ iandt = checked_malloc(sizeof(*iandt));
	iandt->i = i; iandt->t = t;
	return iandt;
}

IntAndTable_ interpExp(A_exp e, Table_ t);

Table_ interpStm(A_stm s, Table_ t)
{
	if (s->kind == A_compoundStm) {
		Table_ new_t = interpStm(s->u.compound.stm1, t);
		return interpStm(s->u.compound.stm2, new_t);
	} 
	else if (s->kind == A_assignStm) {
		IntAndTable_ iandt = interpExp(s->u.assign.exp, t);
		return Table(s->u.assign.id, iandt->i, iandt->t);
	} else { /* print statement */
		A_expList expList = s->u.print.exps;
		A_expList next = expList;
		Table_ new_t = t;
		while (next->kind != A_lastExpList) {
			IntAndTable_ iandt = interpExp(expList->u.pair.head, new_t);
			new_t = iandt->t;
			printf("%d ", iandt->i);
			next = next->u.pair.tail;
		}
		IntAndTable_ iandt = interpExp(next->u.last, new_t);
		new_t = iandt->t;
		printf("%d\n", iandt->i);
		return new_t;
	}
}

IntAndTable_ interpExp(A_exp e, Table_ t)
{
	if (e->kind == A_idExp) {
		return IntAndTable(lookup(t, e->u.id), t);
	} else if (e->kind == A_numExp) {
		return IntAndTable(e->u.num, t);
	} else if (e->kind == A_opExp) {
		IntAndTable_ left_iandt = interpExp(e->u.op.left, t);
		IntAndTable_ right_iandt = interpExp(e->u.op.right, left_iandt->t);
		int result = 0;
		switch (e->u.op.oper) {
			case A_plus:
				result = left_iandt->i + right_iandt->i;
				break;
			case A_minus:
				result = left_iandt->i - right_iandt->i;
				break;
			case A_times:
				result = left_iandt->i * right_iandt->i;
				break;
			case A_div:
				result = left_iandt->i / right_iandt->i;
				break;
			default:
				break;
		}
		return IntAndTable(result, right_iandt->t);
	} else { /* eseqExp */
		Table_ new_t = interpStm(e->u.eseq.stm, t);
		return interpExp(e->u.eseq.exp, new_t);
	}
}

void interp(A_stm stm)
{
	Table_ init_table = NULL;
	interpStm(stm, init_table);
}
