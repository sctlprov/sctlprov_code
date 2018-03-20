#include "bcg_user.h"
#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <stdio.h>

static BCG_TYPE_OBJECT_TRANSITION bcg_graph = NULL;
static BCG_TYPE_STATE_NUMBER bcg_ini = 0;
static BCG_TYPE_STATE_NUMBER bcg_s1 = 0;
static BCG_TYPE_LABEL_NUMBER bcg_label_number = 0;
static BCG_TYPE_STATE_NUMBER bcg_s2 = 0;


void init(char* filename)
{
    BCG_TYPE_OBJECT_TRANSITION bg;
    BCG_INIT();
    BCG_OT_READ_BCG_BEGIN(filename, &bg, 1);
    bcg_graph = bg;
}

int nb_states() {
    return BCG_OT_NB_STATES(bcg_graph);
    // return 1;
}


CAMLprim value read_bcg(value v) {
    CAMLparam1(v);
    CAMLlocal1(info);
    // CAMLlocal4(a,b,c,d);
    CAMLlocal1(a);
    init(String_val(v));
    a = bcg_ini;
    CAMLreturn (Val_int(a));
}

/*
    Find the transitions for the given state s.
*/
CAMLprim value trans(value v) {
    CAMLparam1(v);
    CAMLlocal5(clist, cons, ctuple, label_number, s2);
    CAMLlocal1(label_visible);
    clist = Val_emptylist;
    bcg_s1 = Int_val(v);
    BCG_OT_ITERATE_P_LN(bcg_graph, bcg_s1, bcg_label_number, bcg_s2)
    {
        ctuple = caml_alloc_tuple(4);
        label_number = bcg_label_number;
        s2 = bcg_s2;
        // ls = bcg_label_string;
        label_visible = BCG_OT_LABEL_VISIBLE(bcg_graph, bcg_label_number);
        Store_field(ctuple, 0, Val_int(label_number));
        // Store_field(ctuple, 1, caml_copy_string(ls));
        Store_field(ctuple, 1, Val_bool(label_visible));
        Store_field(ctuple, 2, Val_int(s2));
        cons = caml_alloc(2,0);
        Store_field(cons, 0, ctuple);
        Store_field(cons, 1, clist);
        clist = cons;
    }
    BCG_OT_END_ITERATE;
    CAMLreturn (clist);
}


/*
    Stop reading bcg file, and release resources
*/
CAMLprim value close_bcg(value v) {
    BCG_OT_READ_BCG_END(&bcg_graph);
    return v;
}
