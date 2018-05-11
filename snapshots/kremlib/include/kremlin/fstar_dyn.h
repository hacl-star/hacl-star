#ifndef __FSTAR_DYN_H
#define __FSTAR_DYN_H

/******************************************************************************/
/* Implementing FStar.Dyn.fst                                                 */
/******************************************************************************/

typedef void *FStar_Dyn_dyn;

static inline FStar_Dyn_dyn FStar_Dyn_mkdyn_(void *x) {
  return x;
}

#endif
