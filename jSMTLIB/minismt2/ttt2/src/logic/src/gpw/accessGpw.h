/* File generated from ??? */

#ifndef _CAMLIDL_ACCESSGPW_H
#define _CAMLIDL_ACCESSGPW_H


#ifdef _WIN32
#pragma pack(push,8) /* necessary for COM interfaces */
#endif

#ifdef __cplusplus
#include "Int.h"

//  taken from main.h in Minisat+:

enum SolverT  { st_MiniSat, st_SatELite };
enum ConvertT { ct_Sorters, ct_Adders, ct_BDDs, ct_Mixed, ct_Undef };
enum GpwT     { gt_none, gt_positive, gt_negative, gt_low, gt_high, gt_both }; 

// -- output options -
extern bool     opt_satlive;
extern bool     opt_ansi;
extern char*    opt_cnf;
extern int      opt_verbosity;
extern bool     opt_try;

// -- solver options:
extern SolverT  opt_solver;
extern ConvertT opt_convert;
extern ConvertT opt_convert_goal;
extern GpwT     opt_convert_gpw;
extern bool     opt_convert_bdd_monotonic;
extern bool     opt_convert_bdd_binary_decomposition;
extern bool     opt_convert_bdd_interval;
extern bool     opt_convert_bdd_increasing_order;
extern bool     opt_convert_weak;
extern bool     opt_keep_monotonic;
extern double   opt_bdd_thres;
extern double   opt_sort_thres;
extern double   opt_goal_bias;
extern Int      opt_goal;
extern bool     opt_branch_pbvars;
extern int      opt_polarity_sug;

extern bool     opt_model_check;

void reportf(const char* format, ...);  
#endif

#ifdef __cplusplus
#define _CAMLIDL_EXTERN_C extern "C"
#else
#define _CAMLIDL_EXTERN_C extern
#endif

_CAMLIDL_EXTERN_C void initPbSolving(/*in*/ int n_var, /*in*/ int n_con, /*in*/ int cmd);

_CAMLIDL_EXTERN_C void setOption(/*in*/ char o[]);

_CAMLIDL_EXTERN_C void addConstraint(/*in*/ char *ps[], /*in*/ int *cs, /*in*/ int n_p, /*in*/ int rhs, /*in*/ int ineq);

_CAMLIDL_EXTERN_C int solvePb(/*in*/ char *result[]);

#ifdef _WIN32
#pragma pack(pop)
#endif


#endif /* !_CAMLIDL_ACCESSMINISATP_H */
