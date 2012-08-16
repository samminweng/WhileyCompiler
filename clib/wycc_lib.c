/*
 * wycc_lib.c
 *
 * This is a library of support routines for programs written in
 * the Whiley language when translated into C (ala gcc)
 *
 * This file is part of the Whiley Development Kit (WDK).
 *
 * The Whiley Development Kit is free software; you can redistribute 
 * it and/or modify it under the terms of the GNU General Public 
 * License as published by the Free Software Foundation; either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The Whiley Development Kit is distributed in the hope that it 
 * will be useful, but WITHOUT ANY WARRANTY; without even the 
 * implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR 
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public 
 * License along with the Whiley Development Kit. If not, see 
 * <http://www.gnu.org/licenses/>
 */

/*
 * to do:
 * * set up main method registry so that there can be multiples
 * * set up type registry routines.
 */

#include "../lib/wycc_lib.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * ******************************
 * wycc infrastructure
 * ******************************
 */

/*
 * just in case we need to refer to them from some routine other than main
 */
static int	orig_argc;
static char**	orig_argv;
static char**	orig_envp;

/*
 * storage for the type registry.
 * indexes were off by 1 - to reserve 0 for not assigned.
 * now Any is 0
 * and None is -1
 * simple objects of type any or none have no contents
 * complex objects with subtype none have no contents
 * complex objects with subtype any must accept all other types
 */

static char* wy_type_names[] = {
    /* None */
#define Wy_None	-1
    /* Any */
#define Wy_Any	0
    "any",
    /* primative string, ie. array of unboxed bytes*/
#define Wy_String	1
    "string",
    /* primative integer, it a long instead of pointer */
#define Wy_Int		2
    "int",
    /* a wide integer - unbounded */
#define Wy_WInt		3
    "wint",
    /* a primative list, ie. array of (boxed) objs */
#define Wy_List		4
    "list",
    /* a set */
#define Wy_Set		5
    "set",
    /* a map */
#define Wy_Map		6
    "map",
    /* a record */
#define Wy_Record	7
    "record",
    /*the field names of a record */
#define Wy_Fields	8
    "fields",
    /* a constant string (in code space, not heap */
#define Wy_CString	9
    "string",
    /* a single character */
#define Wy_Char		10
    "char",
#define Wy_Type_Max	10
    (char *) NULL
};

/*
 * DETAILED OBJECT DESCRIPTIONS
 *
 * ie, what does obj->ptr really point to.
 *
 * Wy_None	ptr must be void
 * Wy_Any	ptr must be void
 * Wy_CString
 * Wy_String	ptr to null terminated char[].
 * Wy_Char	ptr is char
 * Wy_Int	ptr is long
 * Wy_WInt	TBD
 * Wy_List	ptr to block:
 *		member count
 *		alloc size
 *		array of obj ptrs
 * Wy_Set	ptr to block:
 *		member type
 *		member count
 *		chunk:
 *			branch count
 *			* {
 *				branch link
 *				value
 *			}
 *			value ...
 *			level_chunk link
 * Wy_Map	ptr to block:
 *		member type
 *		member count
 *		chunk:
 *			branch count
 *			* {
 *				branch link
 *				value
 *				key
 *			}
 *			{
 *				value
 *				key
 *			} ...
 *			level_chunk link
 *
 *
 */
/*
 * we need comparitor functions for all object types
 */
static int wycc_comp_gen(wycc_obj* lhs, wycc_obj* rhs);
static int wycc_comp_str(wycc_obj* lhs, wycc_obj* rhs);
static int wycc_comp_int(wycc_obj* lhs, wycc_obj* rhs);
static int wycc_comp_wint(wycc_obj* lhs, wycc_obj* rhs);
static int wycc_comp_obj(wycc_obj* lhs, wycc_obj* rhs);

typedef int (*Wycc_Comp_Ptr)(wycc_obj* lhs, wycc_obj* rhs);

wycc_initor* wycc_init_chain = NULL;

static void* wycc_fields_master = NULL;

void wycc_chunk_rebal(int payl, void** p, void** chunk, long at, long deep);

/*
 * wycc+wyil needs a unix/c standard starting routine.
 * **** to be changed ****
 * * whiley may have more than one main (with different signatures
 *    and may need to have them registered from each .o file linked in.
 * * these routines and all the other .o files need to agree about
 *    various type information.
 */
int main(int argc, char** argv, char** envp) {
    int idx;
    char* argp;
    wycc_initor* ini;
    wycc_obj* sys;

    orig_argc = argc;
    orig_argv = argv;
    orig_envp = envp;
    wycc_debug_flag = 0;
    for (idx=1; idx < argc ; idx++) {
	argp = argv[idx];
	if (strcmp(argp, "-D") == 0) {
	    wycc_debug_flag = 1;
	};
    };
    if (wycc_debug_flag) {
	if (wycc_init_chain == NULL) {
	    fprintf(stderr, "wycc_init_chain is null\n");
	};
    };
    for (ini= wycc_init_chain; ini != NULL; ) {
	ini->function();
	ini = (wycc_initor*)ini->nxt;
    };
    sys = wycc_box_int(1);	/* **** KLUDGE **** */
    wycc__main(sys);
    return 0;
}

/* -------------------------------
 *  internal routines
 * -------------------------------
 *
 * given a long mask it down to its most significant bit
 */
static wycc_high_bit(long itm) {
    int tmpa, tmpb;

    tmpb = 0;
    for (tmpa= itm; tmpa > 0; tmpa &= (tmpa-1)) {
	tmpb = tmpa;
    }
    if (wycc_debug_flag) {
	fprintf(stderr, "wycc_high_bit(%d) => %d\n", itm, tmpb);
    }
    return tmpb;
}

/* -------------------------------
 *  Routines for basic support of typed objects
 * -------------------------------
 *
 * given a text string, box it in a wycc_obj
 */
wycc_obj* wycc_box_str(char* text) {
    wycc_obj* ans;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_String;
    ans->cnt = 1;
    ans->ptr = (void*) text;
    return ans;
}

/*
 * given a text string, box it in a wycc_obj
 */
wycc_obj* wycc_box_cstr(char* text) {
    wycc_obj* ans;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_CString;
    ans->cnt = 1;
    ans->ptr = (void*) text;
    return ans;
}

/*
 * given an char, box it in a wycc_obj
 */
wycc_obj* wycc_box_char(char x) {
    wycc_obj* ans;
    int tmp;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_Char;
    ans->cnt = 1;
    tmp = (int) x;	/* **** kludge */
    ans->ptr = (void *) tmp;	/* **** kludge */
    return ans;
}

/*
 * given an int (32 bits), box it in a wycc_obj
 */
wycc_obj* wycc_box_int(int x) {
    wycc_obj* ans;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_Int;
    ans->cnt = 1;
    ans->ptr = (void*) x;	/* **** kludge */
    return ans;
}

/*
 * given an long (64 bits), box it in a wycc_obj
 */
wycc_obj* wycc_box_long(long x) {
    wycc_obj* ans;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_Int;
    ans->cnt = 0;
    ans->ptr = (void*) x;	/* **** kludge */
    return ans;
}

/*
 * given a count, setup a list object big enough to accept them.
 * 
 */
wycc_obj* wycc_list_new(long siz) {
    wycc_obj* ans;
    long tmp;
    size_t raw;
    void** p;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_List;
    tmp = 2 * wycc_high_bit(siz+2);
    p = (void**) calloc(tmp, sizeof(void *));
    p[0] = (void *) 0;
    p[1] = (void *) tmp;
    ans->ptr = (void *) p;
    ans->cnt = 1;
    return ans;
}

wycc_obj* wycc_list_get(wycc_obj* lst, long at) {
    void** p = lst->ptr;

    if (lst->typ != Wy_List) {
	fprintf(stderr, "Help needed in wycc_list_get for type %d\n", lst->typ);
	exit(-3);
    };
    if (at >= (long) p[0]) {
	return NULL;
    };
    /* **** Does this need to inc the ref count */
    return (wycc_obj*) p[2+at];
}

void wycc_list_add(wycc_obj* lst, wycc_obj* itm) {
    void** p = lst->ptr;
    long at, tmp;
    size_t raw;

    if (lst->typ != Wy_List) {
	fprintf(stderr, "Help needed in wycc_list_add for type %d\n", lst->typ);
	exit(-3);
    };
    tmp = (long) p[1];
    at = ((long) p[0]) +1;
    p[0] = (void *) at;
    if ((at+2) >= tmp) {
	tmp *= 2;
        raw = tmp * sizeof(void *);
	p = (void **) realloc(p, raw);
	if (p == NULL) {
	    fprintf(stderr, "ERROR: realloc failed\n");
	    exit(-4);
	};
	p[1] = (void *) tmp;
	lst->ptr = p;
    };
    p[1 + at] = (void *) itm;
    itm->cnt++;
    return;
}

/*
 * given a simple type, setup an empty set object
 * 
 */
#define WYCC_SET_CHUNK 8
wycc_obj* wycc_set_new(int typ) {
    wycc_obj* ans;
    long tmp;
    void** p;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_Set;
    tmp = WYCC_SET_CHUNK + 2;
    p = (void**) calloc(tmp, sizeof(void *));
    p[0] = (void *) typ;
    p[1] = (void *) 0;
    ans->ptr = (void *) p;
    ans->cnt = 1;
    return ans;
}

void wycc_set_add(wycc_obj* lst, wycc_obj* itm) {
    void** p = lst->ptr;
    void** chunk;
    void** new;
    long at, typ, cnt, deep, idx, cp;
    size_t raw;
    wycc_obj* tst;
    int end;

    if (lst->typ != Wy_Set) {
	fprintf(stderr, "Help needed in wycc_set_add for type %d\n", lst->typ);
	exit(-3);
    };
    /* Wy_None */
    typ = (long) p[0];
    if (typ == Wy_None) {
	typ = itm->typ;
	p[0] = (void *) typ;
    } else if (typ == Wy_Any) {
    } else if (typ != itm->typ) {
	//fprintf(stderr, "Help needed in wycc_set_add for multi-types \n");
	//exit(-3);
	p[0] = (void *) Wy_Any;
    };
    if ((typ < 0) || (typ > Wy_Type_Max)){
	fprintf(stderr, "Help needed in wycc_set_add for types %d\n", typ);
	exit(-3);
    };
    /* cnt = (long) p[1]; */
    at = 0;
    chunk = &(p[2]);
    if (((long) p[1]) <1) {
	/* add first member to empty set */
	chunk[0] = (void *) 0;
	chunk[1] = (void *) itm;
	itm->cnt++;
	p[1] = (void *) 1;
	return;
    }
    deep = 0;
    /*
     * sequencial search within the chunk
     */
    while (at < ((long) chunk[0])) {
	at++;
	tst = (wycc_obj *) chunk[2*at];
	end = wycc_comp_gen(itm, tst);
	if (end == 0) {
	    return;	/* key match == done */
	};
	if (end < 0) {
	    continue;
	};
	/* the item in question goes before here; ergo down a chunk */
	chunk = chunk[(2*at) - 1];
	at = 0;
	deep++;
    };
    at *= 2;		/* 2 ::= sizeof branch pair */
    /* at -= 1;		/* but not looking at pairs anymore */
    /*at += 1;		/* but not looking at pairs anymore */
    while (at < (WYCC_SET_CHUNK -1)) {
	at++;
	tst = (wycc_obj *) chunk[at];
	if (tst == (wycc_obj *) NULL) {
	    chunk[at] = (void *) itm;
	    itm->cnt++;
	    p[1]++;
	    wycc_chunk_rebal(0, p, chunk, at, deep);
	    return;
	}
	end = wycc_comp_gen(itm, tst);
	if (end == 0) {
	    return;	/* key match == done */
	};
	if (end < 0) {
	    break;
	};
    };
    if (end < 0) {
	at++;
    };
    /* this is a definite add */
    p[1]++;
    itm->cnt++;
    /*    if (at == (WYCC_SET_CHUNK -2)) {
	/* Need to insert just before or just after the end of a full chunk */
    tst = chunk[WYCC_SET_CHUNK -2];
    if (tst != (void *) NULL) {
	/* need to insert in a full chunk */
	/* split chunk into 2, expanding down deeper */
	new = (void**) calloc(WYCC_SET_CHUNK, sizeof(void *));
	if (new == (void **) NULL) {
	    fprintf(stderr, "ERROR: calloc failed new chunk\n");
	    exit(-4);
	};
	cnt = 2 * (long) chunk[0];
	/* push the bigger section down */
	if (cnt > (WYCC_SET_CHUNK /2)) {
	    /* the bigger is the branch section */
	    cnt += 1;	/* include the branch counter */
	    for (idx= 0; idx < cnt ;idx++) {
		new[idx] = chunk[idx];
	    };
	    /* we are forming a branch out of all the branch pairs */
	    /* but that branch pairs up with the first leaf */
	    chunk[0] = (void *) 1;
	    chunk[1] = (void *) new;
	    cp = 2;
	    for (; idx < (WYCC_SET_CHUNK - 1); idx++) {
		if (idx == at) {
		    chunk[cp++] = itm;
		};
		chunk[cp++] = chunk[idx];
	    };
	    /* we have to special special case an insert after the end */
	    if (idx == at) {
		chunk[cp++] = itm;
	    };
	    for (; cp < (WYCC_SET_CHUNK - 1); cp++) {
		chunk[cp++] = (void *) NULL;
	    };
	} else {
	    /* bigger is the leaf section */
	    cnt+= 1;	/* adjust for the branch counter */
	    new[0] = 0;
	    cp = 1;
	    for (idx= cnt; idx < (WYCC_SET_CHUNK - 1); idx++) {
		if (idx == at) {
		    new[cp++] = itm;
		};
		new[cp++] = chunk[idx];
		chunk[idx] = (void *) NULL;
	    };
	    /* we have to special special case an insert after the end */
	    if (idx == at) {
		new[cp++] = itm;
	    };
	    /* now steal back the last leaf to use in a new branch pair */
	    chunk[cnt++] = (void *) new;
	    chunk[cnt] = new[--cp];	/* last value becomes branch pair */
	    new[cp] = (void *) NULL;
	    
	};
	/**** rebalance tree */
	return;
    };
    /* need to insert item before at and we have room for it. */
    /* it is a leaf */
    for (idx= (WYCC_SET_CHUNK - 1); idx > at ; idx--) {
	chunk[idx] = chunk[idx - 1];
    }
    chunk[at] = itm;
    /**** rebalance tree */
    return;
}

/*
 * given a simple type, setup an empty map object
 * 
 */
#define WYCC_MAP_CHUNK 8*3
wycc_obj* wycc_map_new(int typ) {
    wycc_obj* ans;
    long tmp;
    void** p;

    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_Map;
    tmp = WYCC_MAP_CHUNK + 2;
    p = (void**) calloc(tmp, sizeof(void *));
    p[0] = (void *) typ;
    p[1] = (void *) 0;
    ans->ptr = (void *) p;
    ans->cnt = 1;
    return ans;
}

void wycc_map_add(wycc_obj* lst, wycc_obj* key, wycc_obj* itm) {
    void** p = lst->ptr;
    void** chunk;
    void** new;
    long at, typ, cnt, deep, idx, cp;
    size_t raw;
    wycc_obj* tst;
    int end;

    if (lst->typ != Wy_Map) {
	fprintf(stderr, "Help needed in wycc_map_add for type %d\n", lst->typ);
	exit(-3);
    };
    typ = (long) p[0];
    if (typ == Wy_None) {
	typ = key->typ;
	p[0] = (void *) typ;
    } else if (typ == Wy_Any) {
    } else if (typ != itm->typ) {
	//fprintf(stderr, "Help needed in wycc_map_add for multi-types \n");
	//exit(-3);
	p[0] = (void *) Wy_Any;
    };
    if ((typ < 0) || (typ > Wy_Type_Max)){
	fprintf(stderr, "Help needed in wycc_map_add for types %d\n", typ);
	exit(-3);
    };
    at = 0;
    chunk = &(p[2]);
    if (((long) p[1]) <1) {
	/* add first member to empty map */
	chunk[0] = (void *) 0;
	chunk[1] = (void *) itm;
	chunk[2] = (void *) key;
	itm->cnt++;
	key->cnt++;
	p[1] = (void *) 1;
	return;
    }
    /*
     * sequencial search within the chunk
     */
    while (at < ((long) chunk[0])) {
	at++;
	tst = (wycc_obj *) chunk[3*at];
	end = wycc_comp_gen(key, tst);
	if (end == 0) {
	    /* key match == done ; swap the value stored */
	    tst = (wycc_obj *) chunk[(3*at) -1];
	    chunk[(3*at) -1] = (void *) itm;
	    wycc_deref_box(tst);
	    return;
	};
	if (end < 0) {
	    continue;
	};
	/* the item in question goes before here; ergo down a chunk */
	chunk = chunk[(3*at) - 2];
	at = 0;
	deep++;
    };
    at *= 3;		/* 3 ::= sizeof branch value key triplet */
    while (at < (WYCC_MAP_CHUNK -2)) {
	at += 2;
	tst = (wycc_obj *) chunk[at];
	if (tst == (wycc_obj *) NULL) {
	    chunk[at]    = (void *) key;
	    chunk[at -1] = (void *) itm;
	    itm->cnt++;
	    key->cnt++;
	    p[1]++;
	    wycc_chunk_rebal(0, p, chunk, at, deep);
	    return;
	}
	// end = compar(key, tst);
	end = wycc_comp_gen(key, tst);
	if (end == 0) {
	    /* key match == done ; swap the value stored */
	    tst = (wycc_obj *) chunk[at -1];
	    chunk[at -1] = (void *) itm;
	    wycc_deref_box(tst);
	    return;	/* key match == done */
	};
	if (end < 0) {
	    break;
	};
    };
    if (end < 0) {
	at += 2;
    };
    /* this is a definite add */
    p[1]++;
    itm->cnt++;
    key->cnt++;
	/* Need to insert just before or just after the end of a full chunk */
    tst = chunk[WYCC_MAP_CHUNK -3];
    if (tst != (void *) NULL) {
	/* need to insert in a full chunk (noo room for more) */
	/* split chunk into 2, expanding down deeper */
	new = (void**) calloc(WYCC_MAP_CHUNK, sizeof(void *));
	if (new == (void **) NULL) {
	    fprintf(stderr, "ERROR: calloc failed new chunk\n");
	    exit(-4);
	};
	cnt = 3 * (long) chunk[0];
	/* push the bigger section down */
	if (cnt > (WYCC_MAP_CHUNK /2)) {
	    /* the bigger is the branch section */
	    cnt += 1;	/* include the branch counter */
	    for (idx= 0; idx < cnt ;idx++) {
		new[idx] = chunk[idx];
	    };
	    /* we are forming a branch out of all the branch triples */
	    /* but that branch pairs up with the first leaf */
	    chunk[0] = (void *) 1;
	    chunk[1] = (void *) new;
	    cp = 2;
	    for (; idx < (WYCC_SET_CHUNK - 2); ) {
		if (idx == at-1) {
		    chunk[cp++] = itm;
		    chunk[cp++] = key;
		};
		chunk[cp++] = chunk[idx++];
		chunk[cp++] = chunk[idx++];
	    };
	    /* we have to special special case an insert after the end */
	    if (idx == at-1) {
		chunk[cp++] = itm;
		chunk[cp++] = key;
	    };
	    for (; cp < (WYCC_SET_CHUNK - 1); cp++) {
		chunk[cp++] = (void *) NULL;
	    };
	} else {
	    /* bigger is the leaf section */
	    cnt+= 1;	/* adjust for the branch counter */
	    new[0] = 0;
	    cp = 1;
	    for (idx= cnt; idx < (WYCC_SET_CHUNK - 2); ) {
		if (idx == at-1) {
		    new[cp++] = itm;
		    new[cp++] = key;
		};
		new[cp++] = chunk[idx];
		chunk[idx++] = (void *) NULL;
		new[cp++] = chunk[idx];
		chunk[idx++] = (void *) NULL;
	    };
	    /* we have to special special case an insert after the end */
	    if (idx == at-1) {
		new[cp++] = itm;
		new[cp++] = key;
	    };
	    /* now steal back the last leaf to use in a new branch pair */
	    chunk[cnt++] = (void *) new;
	    chunk[cnt++] = new[cp-2];	/* last value becomes branch pair */
	    chunk[cnt++] = new[cp-1];	/* last value becomes branch pair */
	    new[cp-2] = (void *) NULL;
	    new[cp-1] = (void *) NULL;
	};
	/**** rebalance tree */
	return;
    };
    /* need to insert item before at and we have room for it. */
    /* it is a leaf */
    for (idx= (WYCC_MAP_CHUNK - 1); idx > (at-1) ; idx--) {
	chunk[idx] = chunk[idx - 1];
    }
    chunk[at--] = key;
    chunk[at]   = itm;
    /**** rebalance tree */
    return;
}

/*
 * given a set (a chunked tree), rebalance it.
 * a chunk, an index into it, and a depth gage may be given as hints.
 */
void wycc_chunk_rebal(int payl, void** p, void** chunk, long at, long deep){
    return;
}

/*
 * given a wycc_obj, reduce the reference count.
 * when there are no more references reclaim the box.
 * if the flag is set (not zero), reclaim the underlying data.
 */

static void wycc_dealloc_typ(void* ptr, int typ);
wycc_obj* wycc_deref_box(wycc_obj* itm) {
    void* ptr;
    int typ;

    if (--itm->cnt > 0) {
	return itm;
    };
    ptr = itm->ptr;
    typ = itm->typ;
    if (wycc_debug_flag) {
	fprintf(stderr, "note: deallocing box for typ %d\n", typ);
    };
    free(itm);
    if (typ == Wy_Int) {
	return (wycc_obj *) NULL;
    };
    if (typ == Wy_CString) {
	return (wycc_obj *) NULL;
    };
    if (typ == Wy_Char) {
	return (wycc_obj *) NULL;
    };
    wycc_dealloc_typ(ptr, typ);
    return (wycc_obj *) NULL;
}

static void wycc_dealloc_set_chunk(void** chunk) {
    fprintf(stderr, "deallocating chunk of set\n");
    return;
}

static void wycc_dealloc_typ(void* ptr, int typ){
    long siz, idx;
    void** p = (void**) ptr;
    wycc_obj* itm;

    if (typ == Wy_String) {
        free(ptr);
	return;
    };
    if (typ == Wy_List) {
	siz = (long) p[0];
	for (idx= 0; idx < siz; idx++) {
	    itm = (wycc_obj*) p[2+ idx]; 
	    wycc_deref_box(itm);
	}
        free(ptr);
	return;
    };
    if (typ == Wy_Set) {
	void** chunk = &(p[2]);
	wycc_dealloc_set_chunk(chunk);
	fprintf(stderr, "Fail: no support for set in dealloc\n");
	exit(-3);
    }
    if (typ == Wy_Map) {
	fprintf(stderr, "Fail: no support for map in dealloc\n");
	exit(-3);
    }
    if (typ == Wy_Record) {
	fprintf(stderr, "Fail: no support for record in dealloc\n");
	exit(-3);
    }
    fprintf(stderr, "ERROR: unrecognized type (%d) in dealloc\n", typ);
    exit(-3);
}

/*
 * ------------------------------
 * wycc comparison routines for B things
 *
 * each returns      -1,  0, or 1
 * corresponding to  ab, aa,   ba
 * ------------------------------
 */

static int wycc_comp_gen(wycc_obj* lhs, wycc_obj* rhs){
    int lt = lhs->typ;
    int rt = rhs->typ;

    if (lt == Wy_CString) {
	lt = Wy_String;
    };
    if (rt == Wy_CString) {
	rt = Wy_String;
    };
    if (lt < rt) {
	return -1;
    };
    if (lt > rt) {
	return 1;
    };
    if (lt == Wy_String) {
	return wycc_comp_str(lhs, rhs);
    };
    if (lt == Wy_Int) {
	return wycc_comp_int(lhs, rhs);
    };
    if (lt == Wy_Char) {
	return wycc_comp_int(lhs, rhs);
    };
    fprintf(stderr, "Help needed in wycc_comp_gen for type %d\n", lt);
    exit(-3);
}

static int wycc_comp_str(wycc_obj* lhs, wycc_obj* rhs){
    char *lp, *rp;
    int ans;

    if ((lhs->typ != Wy_String) && (lhs->typ != Wy_CString)) {
	fprintf(stderr, "Help needed in wycc_comp_str for type %d\n", lhs->typ);
	exit(-3);
    };
    if ((rhs->typ != Wy_String) && (rhs->typ != Wy_CString)) {
	fprintf(stderr, "Help needed in wycc_comp_str for type %d\n", rhs->typ);
	exit(-3);
    };
    lp = lhs->ptr;
    rp = lhs->ptr;
    ans =  strcmp(lp, rp);
    if (ans < 0) {
	return -1;
    } else if (ans > 0) {
	return 1;
    };
    return 0;
}

static int wycc_comp_int(wycc_obj* lhs, wycc_obj* rhs){
    int lhv, rhv;

    if (lhs->typ != Wy_Int) {
	fprintf(stderr, "Help needed in wycc_comp_int for type %d\n", lhs->typ);
	exit(-3);
    };
    if (rhs->typ != Wy_Int) {
	fprintf(stderr, "Help needed in wycc_comp_int for type %d\n", rhs->typ);
	exit(-3);
    };
    lhv = (long) lhs->ptr;
    rhv = (long) rhs->ptr;
    if (lhv < rhv) {
	return -1;
    } else if (lhv > rhv) {
	return 1;
    };
    return 0;
}

static int wycc_comp_wint(wycc_obj* lhs, wycc_obj* rhs){
	fprintf(stderr, "Help needed in wycc_comp_wint\n");
	exit(-3);
}

/*
 * here we assume that we cannot reasonably compare the value (contents)
 * of the object, so to force a comparison, we compare their locations
 * in memory.
 */
static int wycc_comp_obj(wycc_obj* lhs, wycc_obj* rhs){
    fprintf(stderr, "Warning: wycc_comp_obj is deprecated.\n");
    if (lhs < rhs) {
	return -1;
    } else if (lhs > rhs) {
	return 1;
    };
    return 0;
}

/*
 * given a numeric object return the size of the number
 * (how many longs it takes to represent it)
 */
static int wycc_wint_size(wycc_obj *itm) {
    if (itm->typ == Wy_Int) {
	return (size_t) 1;
    };
    fprintf(stderr, "Help needed in add for type %d\n", itm->typ);
    exit(-3);
}

int wycc_length_of_list(wycc_obj* itm) {
    void** p = itm->ptr;

    if (itm->typ != Wy_List) {
	fprintf(stderr, "Help length_of_list called for type %d\n", itm->typ);
	exit(-3);
    }
    return (int) p[0];
}

int wycc_length_of_set(wycc_obj* itm) {
    void** p = itm->ptr;
    int rslt;

    if (itm->typ != Wy_Set) {
	fprintf(stderr, "Help length_of_set called for type %d\n", itm->typ);
	exit(-3);
    };
    if (((long) p[0]) == Wy_None) {
	return 0;
    };
    return (int) p[1];
}

int wycc_length_of_map(wycc_obj* itm) {
    void** p = itm->ptr;
    int rslt;

    if (itm->typ != Wy_Map) {
	fprintf(stderr, "Help length_of_map called for type %d\n", itm->typ);
	exit(-3);
    };
    if (((long) p[0]) == Wy_None) {
	return 0;
    };
    return (int) p[1];
}

int wycc_length_of_string(wycc_obj* itm) {
    char* p = (char *) itm->ptr;
    int rslt;

    if ((itm->typ != Wy_String) && (itm->typ != Wy_CString)) {
	fprintf(stderr, "Help length_of_string called for type %d\n", itm->typ);
	exit(-3);
    };
    rslt = strlen(p);
    return rslt;
}

/*
 * some operation need to change an object that is currently being shared
 */
wycc_obj* wycc_cow_string(wycc_obj* str) {
    fprintf(stderr, "Fail: wycc_cow_string not written yet.\n");
    exit(-3);

}

/*
 * some operation need to change an object that is currently being shared
 */
wycc_obj* wycc_cow_list(wycc_obj* lst) {
    wycc_obj* ans;
    wycc_obj* nxt;
    void** p = lst->ptr;
    long at, tmp;
    void** new;

    if (lst->typ != Wy_List) {
	fprintf(stderr, "Help needed in wycc_cow_list for type %d\n", lst->typ);
	exit(-3);
    };
    ans = (wycc_obj*) calloc(1, sizeof(wycc_obj));
    ans->typ = Wy_List;
    tmp = (long) p[1];
    new = (void**) calloc(tmp, sizeof(void *));
    tmp = (long) p[0];
    for (at= 0; at < tmp ; at++) {
	nxt = (wycc_obj*) p[2+at];
	nxt->cnt++;
	new[2+at] = (void *) nxt;
    }
    new[0] = (void *) tmp;
    ans->ptr = (void *) new;
    ans->cnt = 1;
    return ans;
}

/*
 * ******************************
 * wyil opcode implementations
 * ******************************
 */

/*
 * given two operands, a relationship, and a text line
 * returnn if the relationship holds, else print the text and exit.
 */
void wyil_assert(wycc_obj* lhs, wycc_obj* rhs, int rel, char *msg){
    int end;

    if ((rel < 0) || (rel >= Wyil_Relation_Mo)) {
	fprintf(stderr, "Failure: wyil_assert with relation %d\n"
		, rel);
	exit(-3);
    };
    end = wycc_comp_gen(lhs, rhs);
    if (end < 0) {
	if (rel == Wyil_Relation_Lt) {
	    return;
	};
	if (rel == Wyil_Relation_Le) {
	    return;
	};
	if (rel == Wyil_Relation_Ne) {
	    return;
	};
    } else if (end > 0) {
	if (rel == Wyil_Relation_Gt) {
	    return;
	};
	if (rel == Wyil_Relation_Ge) {
	    return;
	};
	if (rel == Wyil_Relation_Ne) {
	    return;
	};
    } else {
	if (rel == Wyil_Relation_Eq) {
	    return;
	};
	if (rel == Wyil_Relation_Le) {
	    return;
	};
	if (rel == Wyil_Relation_Ge) {
	    return;
	};
    };
    fprintf(stderr, msg);
    exit(-4);
}

/*
 * update an element of a string
 */
wycc_obj* wyil_update_string(wycc_obj* str, wycc_obj* osv, wycc_obj* rhs){
    char *txt;
    long lsiz, idx;
    int tmp;

    if (str->typ != Wy_String) {
	fprintf(stderr, "ERROR: string in wyil_update_string is type %d\n"
		, str->typ);
	exit(-3);
    };
    if (osv->typ != Wy_Int) {
	fprintf(stderr
		, "ERROR: offset  value in wyil_update_string is type %d\n"
		, osv->typ);
	exit(-3);
    };
    if (rhs->typ != Wy_Char) {
	fprintf(stderr
		, "ERROR: replacement value in wyil_update_string is type %d\n"
		, rhs->typ);
	exit(-3);
    };
    txt = str->ptr;
    lsiz = strlen(txt);
    idx = (long) osv->ptr;
    if ((idx < 0) || (idx >= lsiz)) {
	fprintf(stderr
		, "ERROR: out of bounds offset value in wyil_update_string\n");
	exit(-4);
    };
    if (str->cnt > 1) {
	str = wycc_cow_string(str);
    };
    tmp = (int) rhs->ptr;
    txt[idx] = (char) tmp;
    return str;
}

/*
 * update an element of a list
 */
wycc_obj* wyil_update_list(wycc_obj* lst, wycc_obj* osv, wycc_obj* rhs){
    void** p = lst->ptr;
    wycc_obj* itm;
    long lsiz, idx;

    if (lst->typ != Wy_List) {
	fprintf(stderr, "ERROR: list in wyil_update_list is type %d\n"
		, lst->typ);
	exit(-3);
    };
    if (osv->typ != Wy_Int) {
	fprintf(stderr, "ERROR: offset  value in wyil_update_list is type %d\n"
		, osv->typ);
	exit(-3);
    };
    lsiz = wycc_length_of_list(lst);
    idx = (long) osv->ptr;
    if ((idx < 0) || (idx >= lsiz)) {
	fprintf(stderr
		, "ERROR: out of bounds offset value in wyil_update_list\n");
	exit(-3);
    };
    if (lst->cnt > 1) {
	lst = wycc_cow_list(lst);
	p = lst->ptr;
    };
    itm = p[2+idx];
    p[2+idx] = rhs;
    rhs->cnt++;
    wycc_deref_box(itm);
    return lst;
}

/*
 * create a list that combines two lists
 */
wycc_obj* wyil_list_comb(wycc_obj* lhs, wycc_obj* rhs){
    wycc_obj* ans;
    wycc_obj* itm;
    long lsiz, rsiz, idx, siz;

    if (lhs->typ != Wy_List) {
	fprintf(stderr, "ERROR: lhs in wyil_list_comb is type %d\n", lhs->typ);
	exit(-3);
    };
    if (rhs->typ != Wy_List) {
	fprintf(stderr, "ERROR: rhs in wyil_list_comb is type %d\n", rhs->typ);
	exit(-3);
    };
    lsiz = wycc_length_of_list(lhs);
    rsiz = wycc_length_of_list(rhs);
    siz = lsiz + rsiz;
    siz += 2;	/* pad it a lttle */
    ans = wycc_list_new(siz);
    for (idx=0 ; idx < lsiz; idx++) {
	itm = wycc_list_get(lhs, idx);
	itm->cnt++;
	wycc_list_add(ans, itm);
    }
    for (idx=0 ; idx < rsiz; idx++) {
	itm = wycc_list_get(rhs, idx);
	itm->cnt++;
	wycc_list_add(ans, itm);
    }
    return ans;
}

/*
 * given a wycc obj return an object that represents the length
 */
wycc_obj* wyil_length_of(wycc_obj* itm) {
    long typ = itm->typ;
    int rslt = 0;

    if (typ == Wy_List) {
	rslt = wycc_length_of_list(itm);
    } else if (typ == Wy_Set) {
	rslt = wycc_length_of_set(itm);
    } else if (typ == Wy_Map) {
	rslt = wycc_length_of_map(itm);
    } else if (typ == Wy_String) {
	rslt = wycc_length_of_string(itm);
    } else if (typ == Wy_CString) {
	rslt = wycc_length_of_string(itm);
    } else {
	fprintf(stderr, "Help needed in lengthOf for type %d\n", itm->typ);
	exit(-3);
    };
    return wycc_box_int(rslt);
}

/*
 * debug using an unboxed string
 */
void wyil_debug_str(char* mesg) {
    ;
    fprintf(stderr, "%s\n", mesg);
    return;
}

/*
 * debug using a wycc_obj
 */
void wyil_debug_obj(wycc_obj* ptr1) {
    char* mesg;
    /* if (ptr1->typ == 1) { */
    if (ptr1->typ == Wy_String) {
	fprintf(stderr, "%s\n", ptr1->ptr);
    } else if (ptr1->typ == Wy_CString) {
	fprintf(stderr, "%s\n", ptr1->ptr);
    } else {
	fprintf(stderr, "Help needed in Debug for type %d\n", ptr1->typ);
    };
    return;
}

/*
 * given two strings, return their concatination
 */
wycc_obj* wyil_strappend(wycc_obj* lhs, wycc_obj* rhs){
    size_t siz, sizl, sizr;
    char* rslt;
    wycc_obj* ans;

    /* **** do we need to support Wy_Char ? */
    if ((lhs->typ != Wy_String) && (lhs->typ != Wy_CString)) {
	fprintf(stderr, "Help needed in strappend for type %d\n", lhs->typ);
	exit(-3);
    };
    if ((rhs->typ != Wy_String) && (rhs->typ != Wy_CString)) {
	fprintf(stderr, "Help needed in strappend for type %d\n", rhs->typ);
	exit(-3);
    };
    sizr = strlen(rhs->ptr);
    sizl = strlen(lhs->ptr); 
    siz = sizl + sizr + 2;		/* pad for terminator and spare */
    rslt = (char*) malloc(siz);
    strncpy(rslt, lhs->ptr, sizl);
    strncpy(rslt+sizl, rhs->ptr, sizr+1);
    return wycc_box_str(rslt);
}

wycc_obj* wyil_add(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) + ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in add for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_sub(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) - ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in add for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_bit_and(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;
    /* wycc_obj* ans;*/

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) & ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in bit_and for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_bit_ior(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;
    /* wycc_obj* ans;*/

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) | ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in bit_or for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_bit_xor(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;
    /* wycc_obj* ans;*/

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) ^ ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in bit_xor for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_div(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) / ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in div for wide ints (%d)\n", ac);
    exit(-3);
}

wycc_obj* wyil_mod(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac < 2) {
	rslt = ((long) lhs->ptr) % ((long)rhs->ptr); 
	return wycc_box_long(rslt);
    };
    fprintf(stderr, "Help needed in div for wide ints (%d)\n", ac);
    exit(-3);
}

static int wycc_ilog2(long itm){
    int ans = 0;

    if (itm < 0) {
	itm *= -1;
    };
    while (itm > 0) {
	ans++;
	itm >>= 1;
    }
    return ans;
}

wycc_obj* wyil_mul(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc, ac;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    ac = (lc > rc) ? lc : rc;
    if (ac > 1) {
	fprintf(stderr, "Help needed in mul for wide ints (%d)\n", ac);
	exit(-3);
    };
    rslt = (long) lhs->ptr;
    lc = wycc_ilog2(rslt);
    rc = wycc_ilog2((long) rhs->ptr);
    if ((lc + rc) > 62) {
	fprintf(stderr, "Help needed in mul for wide ints (2)\n");
	exit(-3);
    };
    rslt *= (long)rhs->ptr; 
    return wycc_box_long(rslt);
}

wycc_obj* wyil_shift_up(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    if (rc > 1) {
	fprintf(stderr, "ERROR shift to exceed memory\n");
	exit(-4);
    }
    if (lc > 1) {
	fprintf(stderr, "Help needed in shift_up for wide ints (%d)\n", lc);
	exit(-3);
    }
    rslt = (long) rhs->ptr;
    if (rslt > 60*8) {
	fprintf(stderr, "ERROR shift to exceed memory\n");
	exit(-4);
    }
    if (rslt > 60) {
	rslt += 63;
	rslt /= 64;
	fprintf(stderr, "Help needed in shift_up for wide ints (%d)\n", rslt);
	exit(-3);
    }
    rc = rslt;
    rslt = (long) lhs->ptr;
    rslt <<= rc;
    return wycc_box_long(rslt);
}

wycc_obj* wyil_shift_down(wycc_obj* lhs, wycc_obj* rhs){
    long rslt;
    int lc, rc;

    lc = wycc_wint_size(lhs);
    rc = wycc_wint_size(rhs);
    if (rc > 1) {
	rslt = 0;
	return wycc_box_long(rslt);
    }
    if (lc > 1) {
	fprintf(stderr, "Help needed in shift_up for wide ints (%d)\n", lc);
	exit(-3);
    }
    rslt = (long) rhs->ptr;
    if (rslt > 64) {
	rslt = 0;
	return wycc_box_long(rslt);
    }
    rc = rslt;
    rslt = (long) lhs->ptr;
    rslt >>= rc;
    return wycc_box_long(rslt);
}

static wycc_obj* wyil_index_of_list(wycc_obj* lhs, wycc_obj* rhs){
    void** p = lhs->ptr;
    wycc_obj* ans;
    long idx;

    if (rhs->typ != Wy_Int) {
	fprintf(stderr, "Help needed in wyil_index_of_list for type %d\n"
		, rhs->typ);
	exit(-3);
    };
    idx = (long) rhs->ptr;
    if (idx < 0) {
	fprintf(stderr, "ERROR: IndexOf under range for list (%d)", idx);
	exit(-4);
    };
    if (idx >= (long) p[0]) {
	fprintf(stderr, "ERROR: IndexOf over range for list (%d)", idx);
	exit(-4);
    };
    ans = (wycc_obj*) p[2+idx];
    ans->cnt++;
    return ans;
}

static wycc_obj* wyil_index_of_map(wycc_obj* map, wycc_obj* key){
    void** p = map->ptr;
    void** chunk;
    wycc_obj* ans;
    wycc_obj* tst;
    long at, typ, cnt;
    // int (*compar)(wycc_obj* lhs, wycc_obj* rhs);
    int end;

    typ = (long) p[0];
    if (typ == Wy_None) {
	fprintf(stderr, "ERROR: IndexOf for empty map \n");
	exit(-4);
    };
    at = 0;
    chunk = &(p[2]);
    if (((long) p[1]) <1) {
	fprintf(stderr, "ERROR: IndexOf for empty map \n");
	exit(-4);
    }
    // compar = wycc_get_comparator(typ);
    /*
     * sequencial search within the chunk
     */
    while (at < ((long) chunk[0])) {
	at++;
	tst = (wycc_obj *) chunk[3*at];
	// end = compar(key, tst);
	end = wycc_comp_gen(key, tst);
	if (end == 0) {
	    /* key match == done ; swap the value stored */
	    ans = (wycc_obj *) chunk[(3*at) -1];
	    ans->cnt++;
	    return ans;
	};
	if (end < 0) {
	    continue;
	};
	/* the item in question goes before here; ergo down a chunk */
	chunk = chunk[(3*at) - 2];
	at = 0;
    };
    at *= 3;		/* 3 ::= sizeof branch value key triplet */
    while (at < (WYCC_MAP_CHUNK -2)) {
	at += 2;
	tst = (wycc_obj *) chunk[at];
	if (tst == (wycc_obj *) NULL) {
	    fprintf(stderr, "ERROR: key not found IndexOf map \n");
	    exit(-4);
	}
	// end = compar(key, tst);
	end = wycc_comp_gen(key, tst);
	if (end == 0) {
	    /* key match == done ; swap the value stored */
	    ans = (wycc_obj *) chunk[at -1];
	    ans->cnt++;
	    return ans;
	};
	if (end < 0) {
	    break;
	};
    };
    fprintf(stderr, "ERROR: key not found IndexOf map \n");
    exit(-4);

}

static wycc_obj* wyil_index_of_string(wycc_obj* str, wycc_obj* index){
    char *txt;
    long idx;
    char rslt;

    if (index->typ != Wy_Int) {
	fprintf(stderr, "Help needed in wyil_index_of_string for type %d\n"
		, index->typ);
	exit(-3);
    };
    idx = (long) index->ptr;
    if (idx < 0) {
	fprintf(stderr, "ERROR: IndexOf under range for string (%d)", idx);
	exit(-4);
    };
    txt = str->ptr;
    if (idx >= strlen(txt)) {
	fprintf(stderr, "ERROR: IndexOf over range for string (%d)", idx);
	exit(-4);
    };
    rslt = txt[idx];
    return wycc_box_char(rslt);
}

wycc_obj* wyil_index_of(wycc_obj* lhs, wycc_obj* rhs){
    wycc_obj* ans;

    if (lhs->typ == Wy_List) {
	return wyil_index_of_list(lhs, rhs);
    };
    if (lhs->typ == Wy_Map) {
	return wyil_index_of_map(lhs, rhs);
    };
    if (lhs->typ == Wy_String) {
	return wyil_index_of_string(lhs, rhs);
    };
    if (lhs->typ == Wy_CString) {
	return wyil_index_of_string(lhs, rhs);
    };
	fprintf(stderr, "Help needed in wyil_index_of for type %d\n", lhs->typ);
	exit(-3);
}

/*
 * ******************************
 * whiley standard library ie., native methods
 * ******************************
 *
 * Note: there is a double underscore (__) following the "wycc"
 * in these names.
 */

/*
 * given a System object, write a line to the file referred to by out
 */
void wycc__println(wycc_obj* sys, wycc_obj* itm) {
    wycc_obj* alt;
    int tmp;

    if (itm->typ == Wy_String) {
	printf("%s\n", (char *) itm->ptr);
	return;
    };
    if (itm->typ == Wy_CString) {
	printf("%s\n", (char *) itm->ptr);
	return;
    };
    if (itm->typ == Wy_Char) {
	tmp = (int) itm->ptr;
	printf("'%c'\n", (char) tmp);
	return;
    };
    if (itm->typ == Wy_Int) {
	printf("%-.1d\n", (long) itm->ptr);
	return;
    };
    alt = wycc__toString(itm);
    printf("%s\n", alt->ptr);
    wycc_deref_box(alt);
}

static char *wycc__toString_set(void **chunk, char* buf, size_t *isiz) {
    int cnt;
    int idx;
    long tmp;
    wycc_obj* nxt;

    size_t siz = *isiz;
    long at = strlen(buf);

    cnt = ((long) chunk[0]) * 2;
    for (idx = 1; idx < WYCC_SET_CHUNK ; idx++) {
	nxt = (wycc_obj*) chunk[idx];
	if (nxt == NULL) {
	    break;
	};
	if ((idx < cnt) && ((idx % 2) != 0)) {
	    buf = wycc__toString_set((void**) nxt, buf, isiz);
	    at = strlen(buf);
	    continue;
	};
	nxt = wycc__toString(nxt);
	tmp = strlen(nxt->ptr);
	if (siz <= (at+tmp+3)) {
	    if (siz > 512) {
		siz += 1024;
		siz -= 1;
		siz - (siz % 512);
	    } else {
		siz += siz/2;
	    }
	    buf = (char*) realloc((void*)buf, siz);
	};
	if (at > 1) {
	    strcpy((buf+at), ", ");
	    at += 2;
	};
	strcpy((buf+at), nxt->ptr);
	at += tmp;
	wycc_deref_box(nxt);
    }
    *isiz = siz;
    return buf;
}

wycc_obj* wycc__toString(wycc_obj* itm) {
    size_t siz;
    long tmp;
    long cnt, idx, at;
    char *buf;
    char *part;
    char *ptr;
    wycc_obj* nxt;

    if (itm->typ == Wy_String) {
	itm->cnt++;
	return itm;
    };
    if (itm->typ == Wy_CString) {
	itm->cnt++;
	return itm;
    };
    if (itm->typ == Wy_Int) {
	tmp = (int) itm->ptr;
	buf = (char *) malloc(16);
	sprintf(buf, "%-.1d", tmp);
	return wycc_box_str(buf);
    };
    if (itm->typ == Wy_Int) {
	tmp = (int) itm->ptr;
	buf = (char *) malloc(16);
	sprintf(buf, "%-.1d", tmp);
	return wycc_box_str(buf);
    };
    if (itm->typ == Wy_List) {
	cnt = wycc_length_of_list(itm);
	siz = 3 + (cnt * 4);	/* minimalist approx. */
	buf = (char *) malloc(siz);
	buf[0] = '\0';
	strncat(buf, "[", siz);
	at = 1;
	for (idx=0 ; idx < cnt; idx++) {
	    nxt = wycc_list_get(itm, idx);
	    nxt = wycc__toString(nxt);
	    tmp = strlen(nxt->ptr);
	    if (siz <= (at+tmp+3)) {
		siz += (cnt - idx) * 4;
		buf = (char*) realloc((void*)buf, siz);
	    };
	    if (idx > 0) {
		strcpy((buf+at), ", ");
		at += 2;
	    };
	    strcpy((buf+at), nxt->ptr);
	    at += tmp;
	    wycc_deref_box(nxt);
	}
	strcpy((buf+at), "]");
	return wycc_box_str(buf);
    };
    if (itm->typ == Wy_Set) {
	//return wycc_box_cstr("Set");
	cnt = wycc_length_of_set(itm);
	siz = 3 + (cnt * 4);	/* minimalist approx. */
	buf = (char *) malloc(siz);
	buf[0] = '\0';
	strncat(buf, "{", siz);
	at = 1;
	void **p = itm->ptr;
	buf = wycc__toString_set((void**)&(p[2]), buf, &siz);
	at = strlen(buf);
	strcpy((buf+at), "}");
	return wycc_box_str(buf);
    };
    if (itm->typ == Wy_Map) {
	return wycc_box_cstr("Map");
    };
    return wycc_box_cstr("Unknown");
}


/*
;;; Local Variables: ***
;;; c-basic-offset: 4 ***
;;; End: ***
 */
