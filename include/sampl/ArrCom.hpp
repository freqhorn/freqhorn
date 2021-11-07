#ifndef ARRCOM__HPP__
#define ARRCOM__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class ARRfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;
    ExprVector forall_args;
    LAfactory postFac;
    ExprSet pre;
    density postOrAritiesDensity;

    public:

    ARRfactory(ExprFactory &_efac, bool _false) :
        m_efac(_efac), postFac(_efac, false) {};

    void addVar(Expr var)
    {
      vars.push_back(var); // currently, not used. TODO: at least some sanity checks later
    }

    void initializeLAfactory (LAfactory& lf, ExprSet& cands, ExprVector& intVars, int eps)
    {
      for (auto & a : intVars) lf.addVar(a);
      set<cpp_int> arrConsts;
      set<cpp_int> arrCoefs;
      ExprSet normCands;
      for (auto a : cands)
      {
        a = normalizeDisj(a, lf.getVars());
        if (getLinCombCoefs(a, arrCoefs) && getLinCombConsts(a, arrConsts))
          normCands.insert(a);
      }
      for (auto & a : arrConsts) lf.addConst(lexical_cast<cpp_int>(a));
      for (auto & a : arrCoefs) lf.addIntCoef(lexical_cast<cpp_int>(a));

      lf.initialize();
      set<int> orArities;
      vector <LAdisj> laDisjs;
      for (auto & a : normCands)
      {
        LAdisj b;
        lf.exprToLAdisj(a, b);
        laDisjs.push_back(b);
        int ar = b.arity;
        postOrAritiesDensity[ar] ++;
        orArities.insert(ar);
      }

      lf.initDensities(orArities);
      for (auto & b : laDisjs) lf.calculateStatistics(b, b.arity, 0, 0);
      for (auto & ar : orArities) lf.stabilizeDensities(ar, eps, 1);
    }

    void initialize(ExprVector& intVars, ExprSet& arrCands, ExprVector& arrAccessVars, ExprSet& arrRange)
    {
      for (auto & it : arrAccessVars)
        if (bind::isIntConst(it))
        {
          postFac.addVar(it);
          if (find(intVars.begin(), intVars.end(), it) == intVars.end())
            forall_args.push_back(it->left());
        }

      ExprSet se;
      for (auto & a : arrCands)
        filter (a, bind::IsSelect (), inserter(se, se.begin()));

      for (auto & b : se)
        if (isOpX<INT_TY>(typeOf(b)))
          postFac.addVar(b);

      pre = arrRange;
      tmp1 = arrCands;
      tmp2 = intVars;
    }

    ExprSet tmp1;
    ExprVector tmp2;

    void initializeLAfactories()
    {
      initializeLAfactory(postFac, tmp1, tmp2, 0);
    }

    void shrinkArgs(ExprVector& args, ExprSet& shrPre, Expr constr)
    {
      for (auto v = args.begin(); v != args.end(); )
      {
        auto qv = bind::fapp(*v);
        if (contains(constr, qv)) ++v;
        else
        {
          for (auto it = shrPre.begin(); it != shrPre.end(); )
          {
            if (contains (*it, qv)) it = shrPre.erase(it);
            else ++it;
          }
          v = args.erase(v);
        }
      }
    }

    // used for bootstrapping where `cellProperty` is one of the `arrCands`
    Expr getQCand(Expr cellProperty)
    {
      ExprVector args = forall_args;
      ExprSet shrPre = pre;
      shrinkArgs(args, shrPre, cellProperty);
      args.push_back(mk<IMPL>(conjoin(shrPre, m_efac), cellProperty));
      return mknary<FORALL> (args);
    }

    Expr getQCand ()
    {
      LAdisj cellProperty;
      int arity = postOrAritiesDensity.empty() ? 1 :
                    chooseByWeight(postOrAritiesDensity);
      if (postFac.guessTerm(cellProperty, arity, arity))
        return getQCand(postFac.toExpr(cellProperty));
      else
        return NULL;

    }
  };
}


#endif
