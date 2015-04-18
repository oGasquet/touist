/***************************************************************************[PbSolver_convertBdd.C]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "PbSolver.h"
#include "FEnv.h"
#include "Sort.h"
#include "Debug.h"

//=================================================================================================

#define lit2fml(p) id(var(var(p)),sign(p))

static
Pair<Interval<Int>, Formula> buildBDD(const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi, int size, Int sum, Int material_left, Map<Pair< int, Interval<Int> >,Formula>& memo, int max_cost)
{
    Int lower_limit = (lo == Int_MIN) ? Int_MIN : lo - sum;
    Int upper_limit = (hi == Int_MAX) ? Int_MAX : hi - sum;
    // lo - sum <= (Cs[0]*ps[0] + ... + Cs[size]*ps[size]) <= hi - sum

    if (opt_keep_monotonic||opt_convert_bdd_interval||opt_convert_bdd_monotonic)
      assert(upper_limit == Int_MAX);

    /**/if(opt_verbosity >= 2) reportf("# buildBDD\n"),reportf(" size=%d, sum=%d, left=%d, ",size,toint(sum),toint(material_left)),reportf("  lo_limit="), dump(lower_limit),reportf("\n");

    if (lower_limit <= 0 && upper_limit >= material_left)
      return Pair_new( Interval<Int>(Int_MIN,0), _1_);
    else if (lower_limit > material_left || upper_limit < 0)
      return Pair_new( Interval<Int>(1,Int_MAX), _0_);
    else if (FEnv::topSize() > max_cost)
      return Pair_new(Interval<Int>(lower_limit,lower_limit), _undef_);     // (mycket elegant!)

    Interval<Int> K = Interval<Int>(lower_limit,lower_limit);

    Pair< int, Interval<Int> >  key = Pair_new( size, K);
    Formula         ret;

    if (!memo.peek(key, ret)){
      /**/if(opt_verbosity >= 2) reportf("<%d,%d> not found\n",size,toint(lower_limit));
        assert(size != 0);
        size--;
        material_left -= Cs[size];

        Pair< Interval<Int>, Formula> 
	  tt = buildBDD(ps, Cs, lo, hi, size, sum + Cs[size], material_left, memo, max_cost);
        if (tt.snd == _undef_) // return _undef_;
	  return Pair_new(Interval<Int> (lower_limit,lower_limit), _undef_ );

	Pair< Interval<Int>, Formula> 
	  ff = buildBDD(ps, Cs, lo, hi, size, sum, material_left, memo, max_cost);
	if (ff.snd == _undef_) //return _undef_;
	  return Pair_new(Interval<Int> (lower_limit,lower_limit), _undef_ );

	Int tt_beta = tt.fst.fst, tt_gamma = tt.fst.snd;
        Int ff_beta = ff.fst.fst, ff_gamma = ff.fst.snd;
	if(opt_convert_bdd_interval)
	  K = Interval<Int>(max(tt_beta.add(Cs[size]),ff_beta), min(tt_gamma.add(Cs[size]),ff_gamma));
	key = Pair_new( size+1, K);

	/**/if(opt_verbosity >= 2) reportf("tt=["),dump(tt_beta),reportf(","),dump(tt_gamma),reportf("] and "), reportf("ff=["),dump(ff_beta),reportf(","),dump(ff_gamma),reportf("], "),  reportf("for <%d,%d>, ",size+1,toint(lower_limit)), reportf("<%d,[",size+1),dump(K.fst),reportf(","),dump(K.snd),reportf("]> added\n",size+1);

	//	assert(K == newK);  K = newK;
	ret = ITE(lit2fml(ps[size]), tt.snd, ff.snd);
	memo.set(key, ret);

    } 
    /**/ else if(opt_verbosity >= 2) reportf("<%d,%d> found\n",size,toint(lower_limit));

    return Pair_new(K, ret );

}


// New school: Use the new 'ITE' construction of the formula environment 'FEnv'.
//
Formula convertToBdd(const Linear& c, int max_cost)
{
  //    Map<Pair<int,Int>, Formula> memo;
  Map<Pair< int, Interval<Int> >, Formula> memo;

    Int     sum = 0;
    Formula ret;

    if (opt_keep_monotonic)
      assert(c.hi == Int_MAX);

    for (int j = 0; j < c.size; j++)
        sum += c(j);

    vec<Pair<Int,Lit> > Csps;
    vec<Lit> norm_ps;
    vec<Int> norm_Cs;

    if (opt_convert_bdd_binary_decomposition) {  
                       // decompose terms; e.g. 11x into x + 2x + 8x
      for (int i = 0; i < c.size; i++) {
	Int div, rem, co = 1;
	div = c(i);
	while( div > 0 ) {
	  //          reportf("div=%d, rem=%d, co=%d\n",toint(div),toint(rem),toint(co));
	  rem = div % 2;  div = div / 2;
	  if(rem != 0) {
	    Csps.push(Pair_new(co, c[i]));
	    //	    reportf("ps[%d]=", i),dump(c[i]),reportf(", Cs[%d]=", i),dump(co),reportf("\n");
	  }
	  co *= 2;
	}
      }
    } else {
      for (int i = 0; i < c.size; i++) {
	Csps.push(Pair_new(c(i), c[i]));
      }
    }

    if(opt_convert_bdd_increasing_order)
      sortr(Csps);
    else sort(Csps);

      for (int i = 0; i < Csps.size(); i++)
	norm_ps.push(Csps[i].snd), norm_Cs.push(Csps[i].fst);
      /**/if(opt_verbosity >= 2) reportf("ps,Cs="),dump(norm_ps,norm_Cs),reportf(", lo="),dump(c.lo),reportf(", hi="),dump(c.hi),reportf("\n");

      FEnv::push();
      ret = buildBDD(norm_ps, norm_Cs, c.lo, c.hi, Csps.size(), 0, sum, memo, max_cost).snd;
      //      vec<Lit> norm_ps;
      //vec<Int> norm_Cs;
      //for (int i = 0; i < c.size; i++)
      //	norm_ps.push(c[i]), norm_Cs.push(c(i));
      ///**/if(opt_verbosity >= 2) reportf("ps,Cs="),dump(norm_ps,norm_Cs),reportf(", lo="),dump(c.lo),reportf(", hi="),dump(c.hi),reportf("\n");
      //
      //FEnv::push();
      //ret = buildBDD(norm_ps, norm_Cs, c.lo, c.hi, c.size, 0, sum, memo, max_cost).snd;

    //**/reportf("BDD(");  if(ret != _undef_) dump(ret); else reportf("undef"); reportf(")\n");

    if (ret == _undef_)
        FEnv::pop();
    else{
        if (opt_verbosity >= 1)
            reportf("BDD-cost:%5d\n", FEnv::topSize());
        FEnv::keep();
    }

    if(ret != _undef_ && c.dl!=NULL) {
      //      Formula d= id(var(var(*(c.dl))),sign(*(c.dl)));
      //      ret ^= ~d;
      ret ^= ~lit2fml(*(c.dl));
    }
    return ret;
}
