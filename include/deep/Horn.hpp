#ifndef HORN__HPP__
#define HORN__HPP__

#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  inline bool rewriteHelperConsts(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    Expr srcRelation;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (ExprVector& _srcVars, ExprVector& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst, ExprSet& lin)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        srcVars.push_back(invVarsSrc[i]);
        lin.insert(mk<EQ>(_srcVars[i], srcVars[i]));
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        dstVars.push_back(invVarsDst[i]);
        lin.insert(mk<EQ>(_dstVars[i], dstVars[i]));
      }
    }

    void shrinkLocVars()
    {
      for (auto it = locVars.begin(); it != locVars.end();)
        if (contains(body, *it)) ++it;
        else it = locVars.erase(it);
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";
    SMTUtils u;

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> wtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars;
    map<Expr, ExprVector> invVarsPrime;
    map<Expr, vector<int>> outgs;
    vector<vector<int>> prefixes;  // for cycles
    vector<vector<int>> cycles;
    map<Expr, bool> hasArrays;
    bool hasAnyArrays;
    bool hasBV = false;
    int debug;
    set<int> chcsToCheck1, chcsToCheck2, toEraseChcs;
    int glob_ind = 0;

    CHCs(ExprFactory &efac, EZ3 &z3, int d = false) :
      u(efac), m_efac(efac), m_z3(z3), hasAnyArrays(false), debug(d) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->left()))
            if (e->left()->arity() >= 2)
              return true;
      return false;
    }

    void splitBody (HornRuleExt& hr, ExprVector& srcVars, ExprSet& lin)
    {
      getConj (simplifyBool(hr.body), lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FAPP>(cnj) && isOpX<FDECL>(cnj->left()) &&
            find(decls.begin(), decls.end(), cnj->left()) != decls.end())
        {
          Expr rel = cnj->left();
          if (hr.srcRelation != NULL)
          {
            errs () << "Nonlinear CHC is currently unsupported: ["
                    << *hr.srcRelation << " /\\ " << *rel->left() << " -> "
                    << *hr.dstRelation << "]\n";
            exit(1);
          }
          hr.srcRelation = rel->left();
          for (auto it = cnj->args_begin()+1, end = cnj->args_end(); it != end; ++it)
            srcVars.push_back(*it);
          c = lin.erase(c);
        }
        else ++c;
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->left()].size() == 0)
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(i - 1), m_efac);
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY>(arg) && !isOpX<REAL_TY>(arg) &&
              !isOpX<BOOL_TY>(arg) && !isOpX<ARRAY_TY>(arg) &&
              !isOpX<BVSORT> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          Expr var = fapp (constDecl (new_name, a->arg(i)));
          new_name = mkTerm<string> (lexical_cast<string>(var) + "'", m_efac);
          invVars[a->left()].push_back(var);
          invVarsPrime[a->left()].push_back(cloneVar(var, new_name));
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool parse(string smt, bool doElim = true, bool doArithm = true)
    {
      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      chcs.reserve(fp.m_rules.size());

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        hr.body = r->left();
        hr.head = r->right();
        if (isOpX<FAPP>(hr.head))
        {
          if (hr.head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), r->right()) !=
               fp.m_queries.end()))
            addFailDecl(hr.head->left()->left());
          else
            addDecl(hr.head->left());
          hr.dstRelation = hr.head->left()->left();
        }
        else
        {
          if (!isOpX<FALSE>(hr.head)) hr.body = mk<AND>(hr.body, mk<NEG>(hr.head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }
        hasBV |= containsOp<BVSORT>(hr.body);
      }

      if (debug > 0) outs () << "Reserved space for " << chcs.size() << " CHCs and " << decls.size() << " declarations\n";

      // the second loop is needed because we want to distunguish
      // uninterpreted functions used as variables from relations to be synthesized
      for (auto & hr : chcs)
      {
        ExprVector origSrcSymbs;
        ExprSet lin;
        splitBody(hr, origSrcSymbs, lin);
        if (hr.srcRelation == NULL)
        {
          if (hasUninterp(hr.body))
          {
            errs () << "Unsupported format\n";
            errs () << "   " << *hr.body << "\n";
            exit (1);
          }
          hr.srcRelation = mk<TRUE>(m_efac);
        }

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = hr.head->args_begin()+1,
                   end = hr.head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
          hr.head = hr.head->left();
        }

        hr.assignVarsAndRewrite (origSrcSymbs, invVars[hr.srcRelation],
                                 origDstSymbs, invVarsPrime[hr.dstRelation], lin);

        if (doElim)
        {
          hr.body = eliminateQuantifiers(conjoin(lin, m_efac), hr.locVars,
                                                      !hasBV && doArithm, false);
          hr.body = u.removeITE(hr.body);
          hr.body = simplifyArr(hr.body);
          hr.shrinkLocVars();
        }
        else
          hr.body = conjoin(lin, m_efac);
      }

      if (doElim)
      {
        int sz = chcs.size();
        for (int c = 0; c < chcs.size(); c++)
        {
          chcsToCheck1.insert(c);
          chcsToCheck2.insert(c);
        }
        if (!eliminateDecls()) return false;

        // eliminating all at once, otherwise elements at chcsToCheck* need updates
        for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
          chcs.erase(chcs.begin() + *it);
        toEraseChcs.clear();
      }

      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);

      wtoSort();

      if (debug >= 2)
      {
        outs () << (doElim ? "  Simplified " : "  Parsed ") << "CHCs:\n";
        print(debug >= 3);
      }

      return true;
    }

    bool eliminateTrivTrueOrFalse()
    {
      set<int> toEraseChcsTmp;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

        auto c = &chcs[i];
        if (c->isQuery && !c->isFact)
        {
          auto f = find(chcsToCheck1.begin(), chcsToCheck1.end(), i);
          if (f != chcsToCheck1.end())
          {
            if (u.isTrue(c->body))
            {
              // thus, c->srcRelation should be false
              for (int j = 0; j < chcs.size(); j++)
              {
                if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;
                if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), j) != toEraseChcsTmp.end()) continue;

                HornRuleExt* s = &chcs[j];
                if (s->srcRelation == c->srcRelation)
                {
                  // search for vacuous cases where s == inv -> inv2   and   c == inv /\ true -> false
                  // then, inv can only be false, thus s does not give any constraint
                  toEraseChcsTmp.insert(j);  // could erase here, but ther will be a mess with pointers
                }
                else if (s->dstRelation == c->srcRelation)
                {
                  s->isQuery = true;
                  s->dstRelation = failDecl;
                  s->locVars.insert(s->locVars.end(), s->dstVars.begin(), s->dstVars.end());
                  s->dstVars.clear();
                  chcsToCheck1.insert(j);
                  chcsToCheck2.insert(j);
                }
              }
              decls.erase(c->srcRelation);
            }
            chcsToCheck1.erase(f);
          }
        }
        else if (c->isQuery && c->isFact)
          if (u.isSat(c->body))
          {
            outs () << "Counterexample found (during preprocessing)\n";
            return false;
          }
      }

      if (toEraseChcsTmp.empty()) return true;

      for (auto it = toEraseChcsTmp.rbegin(); it != toEraseChcsTmp.rend(); ++it)
      {
        if (debug >= 2) outs () << "  Eliminating vacuous CHC: " << chcs[*it].srcRelation << " -> " << chcs[*it].dstRelation << "\n";
        if (debug >= 3) outs () << "    its body is true: " << chcs[*it].body << "\n";
        toEraseChcs.insert(*it);
      }

      return eliminateTrivTrueOrFalse();     // recursive call
    }

    bool eliminateDecls()
    {
      int preElim = (chcs.size() - toEraseChcs.size());
      if (debug > 0) outs () << "Reducing the number of CHCs: " << preElim <<
                      "; and the number of declarations: " << decls.size() << "...\n";
      if (debug >= 3)
      {
        outs () << "  Current CHC topology:\n";
        print(false);
      }

      if (!eliminateTrivTrueOrFalse()) return false;        // first, remove relations which are trivially false
                                                            // and find any trivially unsatisfiable queries
      Expr declToRemove = NULL;
      vector<int> srcMax, dstMax;
      set<int> toEraseChcsTmp;

      for (auto d = decls.begin(); d != decls.end();)
      {
        vector<int> src, dst;
        for (int i = 0; i < chcs.size(); i++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
          if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

          if (chcs[i].srcRelation == (*d)->left()) src.push_back(i);
          if (chcs[i].dstRelation == (*d)->left()) dst.push_back(i);
        }

        if ((src.size() > 0 && dst.size() > 0) &&
            emptyIntersect(src, dst))
        {

          if (declToRemove != NULL)
            if (declToRemove->arity() > (*d)->arity())
              { ++d; continue; }
          if (declToRemove != NULL)
            if (declToRemove->arity() == (*d)->arity() &&
                src.size() * dst.size() > srcMax.size() * dstMax.size())
              { ++d; continue; }

          srcMax = src;
          dstMax = dst;
          declToRemove = *d;
        }

        if (src.size() == 0) // found dangling CHCs
        {
          toEraseChcsTmp.insert(dst.begin(), dst.end());
          d = decls.erase(d);
        }
        else ++d;
      }

      // first, it will remove dangling CHCs since it's cheaper
      if (declToRemove != NULL && toEraseChcsTmp.empty())
      {
        for (int i : srcMax)
          for (int j : dstMax)
            concatenateCHCs(i, j);

        toEraseChcsTmp.insert(srcMax.begin(), srcMax.end());
        toEraseChcsTmp.insert(dstMax.begin(), dstMax.end());
        decls.erase(declToRemove);
      }

      for (auto a = toEraseChcsTmp.rbegin(); a != toEraseChcsTmp.rend(); ++a)
      {
        if (debug >= 2) outs () << "  Eliminating CHC: " << chcs[*a].srcRelation << " -> " << chcs[*a].dstRelation << "\n";
        toEraseChcs.insert(*a);
      }

      removeTautologies();            // get rid of CHCs that don't add any _new_ constraints
      if (preElim > (chcs.size() - toEraseChcs.size()))
        return eliminateDecls();
      else
      {
        // currently disabled
//        if (!hasAnyArrays) slice();   // remove unrelated constraints and shrink arities of predicates

        int preComb = (chcs.size() - toEraseChcs.size());
        combineCHCs();
        if (preComb > (chcs.size() - toEraseChcs.size()))
          return eliminateDecls();
      }
      return true;
    }

    void concatenateCHCs(int i, int j)
    {
      chcs.push_back(HornRuleExt());
      HornRuleExt* s = &chcs[i];
      HornRuleExt* d = &chcs[j];
      HornRuleExt* n = &chcs.back();
      if (debug >= 2)
      {
        outs () << "  Concatenating two CHCs: "
                << d->srcRelation << " -> " << d->dstRelation << " and "
                << s->srcRelation << " -> " << s->dstRelation << "\n";
      }
      n->srcRelation = d->srcRelation;
      n->dstRelation = s->dstRelation;
      n->srcVars = d->srcVars;
      n->dstVars = d->dstVars;

      ExprVector newVars;
      for (int i = 0; i < d->dstVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->dstVars[i], new_name));
      }
      Expr mergedBody = replaceAll(s->body, s->srcVars, newVars);
      n->dstVars.insert(n->dstVars.end(), d->locVars.begin(), d->locVars.end());
      for (int i = 0; i < d->locVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__loc_var_" + to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->locVars[i], new_name));
      }
      mergedBody = mk<AND>(replaceAll(d->body, n->dstVars, newVars), mergedBody);
      n->locVars = newVars;
      n->locVars.insert(n->locVars.end(), s->locVars.begin(), s->locVars.end());
      n->body = simpleQE(mergedBody, n->locVars);
      n->shrinkLocVars();
      n->dstVars = s->dstVars;
      n->isInductive = n->srcRelation == n->dstRelation;
      n->isFact = isOpX<TRUE>(n->srcRelation);
      n->isQuery = n->dstRelation == failDecl;
      chcsToCheck1.insert(chcs.size()-1);
      chcsToCheck2.insert(chcs.size()-1);
    }

    void removeTautologies()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        auto h = &chcs[i];
        auto f = find(chcsToCheck2.begin(), chcsToCheck2.end(), i);
        if (f != chcsToCheck2.end())
        {
          if (u.isFalse(h->body))
          {
            if (debug >= 2) outs () << "  Eliminating CHC: " << h->srcRelation << " -> " << h->dstRelation << "\n";
            if (debug >= 3) outs () << "    its body is false: " << h->body << "\n";
            toEraseChcs.insert(i);
            continue;
          }
          chcsToCheck2.erase(f);
        }

        bool found = false;
        if (h->isInductive)
        {
          found = true;
          for (int j = 0; j < h->srcVars.size(); j++)
          {
            if (u.isSat(h->body, mkNeg(mk<EQ>(h->srcVars[j], h->dstVars[j]))))
            {
              found = false;
              break;
            }
          }
        }
        if (found)
        {
          if (debug >= 2) outs () << "  Eliminating CHC: " << h->srcRelation << " -> " << h->dstRelation << "\n";
          if (debug >= 3) outs () << "    inductive but does not change vars: " << h->body << "\n";
          toEraseChcs.insert(i);
        }
        else ++h;
      }
    }

    void combineCHCs()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        set<int> toComb = {i};
        HornRuleExt& s = chcs[i];
        for (int j = i + 1; j < chcs.size(); j++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;

          HornRuleExt& d = chcs[j];
          if (s.srcRelation == d.srcRelation && s.dstRelation == d.dstRelation)
          {
            for (int k = 0; k < s.srcVars.size(); k++) assert (s.srcVars[k] == d.srcVars[k]);
            for (int k = 0; k < s.dstVars.size(); k++) assert (s.dstVars[k] == d.dstVars[k]);
            toComb.insert(j);
          }
        }
        if (toComb.size() > 1)
        {
          if (debug >= 2)
          {
            outs () << "    Disjoing bodies of " << toComb.size() << " CHCs: "
                    << s.srcRelation << " -> " << s.dstRelation << "\n";
          }
          ExprVector all;
          for (auto it = toComb.rbegin(); it != toComb.rend(); ++it)
          {
            all.push_back(chcs[*it].body);
            if (*it != i) toEraseChcs.insert(*it);
          }
          s.body = distribDisjoin(all, m_efac);
          chcsToCheck1.insert(i);
          chcsToCheck2.insert(i);
          return combineCHCs();
        }
      }
    }

    // (recursive) multi-stage slicing begins here
    set<int> chcsToVisit;
    map<Expr, ExprSet> varsSlice;

    void updateTodo(Expr decl, int num)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        if (i != num &&
            !chcs[i].isQuery &&
            (chcs[i].srcRelation == decl || chcs[i].dstRelation == decl))
              chcsToVisit.insert(i);
      }
    }

    void slice()
    {
      chcsToVisit.clear();
      varsSlice.clear();
      // first, compute sets of dependent variables
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;

        if (chcs[i].isQuery)
        {
          chcs[i].body = keepQuantifiers(chcs[i].body, chcs[i].srcVars);
          Expr decl = chcs[i].srcRelation;
          filter (chcs[i].body, bind::IsConst(),
            std::inserter (varsSlice[decl], varsSlice[decl].begin ()));
          updateTodo(chcs[i].srcRelation, i);
        }
      }
      while (!chcsToVisit.empty()) slice(*chcsToVisit.begin());

      // now, prepare for variable elimination
      for (auto & d : varsSlice)
      {
//        if (invVars[d.first].size() > d.second.size())
//          outs () << "sliced for " << *d.first << ": " << invVars[d.first].size()
//                  << " -> "    << d.second.size() << "\n";
        ExprSet varsPrime;
        for (auto & v : d.second)
        {
          Expr pr = replaceAll(v, invVars[d.first], invVarsPrime[d.first]);
          varsPrime.insert(pr);
        }

        keepOnly(invVars[d.first], d.second);
        keepOnly(invVarsPrime[d.first], varsPrime);
      }

      // finally, update bodies and variable vectors
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        auto & c = chcs[i];

        if (u.isFalse(c.body) || u.isTrue(c.body)) continue;

        ExprSet bd;
        getConj(c.body, bd);
        for (auto b = bd.begin(); b != bd.end();)
        {
          if (emptyIntersect(*b, invVars[c.srcRelation]) &&
              emptyIntersect(*b, invVarsPrime[c.dstRelation]))
            b = bd.erase(b);
          else ++b;
        }
        if (!c.isFact) c.srcVars = invVars[c.srcRelation];
        if (!c.isQuery) c.dstVars = invVarsPrime[c.dstRelation];
        c.body = conjoin(bd, m_efac);
      }
    }

    void slice(int num)
    {
      HornRuleExt* hr = &chcs[num];
      assert (!hr->isQuery);
      ExprSet srcCore, dstCore, srcDep, dstDep, varDeps, cnjs;

      if (qeUnsupported(hr->body))
      {
        varDeps.insert(hr->srcVars.begin(), hr->srcVars.end());
        varDeps.insert(hr->locVars.begin(), hr->locVars.end());
        varDeps.insert(hr->dstVars.begin(), hr->dstVars.end());
      }
      else
      {
        varDeps = varsSlice[hr->srcRelation];
        filter (getPrecondition(hr), bind::IsConst(),     // all src vars from the preconditions are dependent
                      std::inserter (varDeps, varDeps.begin ()));

        for (auto & v : varsSlice[hr->dstRelation])
          varDeps.insert(replaceAll(v, invVars[hr->dstRelation], hr->dstVars));

        srcCore = varsSlice[hr->dstRelation];
        dstCore = varDeps;

        getConj(hr->body, cnjs);
        while(true)
        {
          int vars_sz = varDeps.size();
          for (auto & c : cnjs)
          {
            ExprSet varsCnj;
            filter (c, bind::IsConst(),
                          std::inserter (varsCnj, varsCnj.begin ()));
            if (!emptyIntersect(varDeps, varsCnj))
              varDeps.insert(varsCnj.begin(), varsCnj.end());
          }
          if (hr->isInductive)
          {
            for (auto & v : varDeps)
            {
              varDeps.insert(replaceAll(v, hr->dstVars, hr->srcVars));
              varDeps.insert(replaceAll(v, hr->srcVars, hr->dstVars));
            }
          }
          if (vars_sz == varDeps.size()) break;
        }
      }

      bool updateSrc = false;
      bool updateDst = false;
      if (!hr->isFact)
      {
        ExprSet& srcVars = varsSlice[hr->srcRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->srcVars.begin(), hr->srcVars.end(), *v) != hr->srcVars.end())
          {
            if (find(srcVars.begin(), srcVars.end(), *v) == srcVars.end())
            {
              updateSrc = true;
              srcVars.insert(*v);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      srcDep = varsSlice[hr->srcRelation];
      dstDep = varDeps;

      if (!hr->isQuery)
      {
        ExprSet& dstVars = varsSlice[hr->dstRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(hr->dstVars.begin(), hr->dstVars.end(), *v) != hr->dstVars.end())
          {
            Expr vp = replaceAll(*v, hr->dstVars, invVars[hr->dstRelation]);
            if (find(dstVars.begin(), dstVars.end(), vp) == dstVars.end())
            {
              updateDst = true;
              dstVars.insert(vp);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      if (!varDeps.empty())
        hr->body = eliminateQuantifiers(hr->body, varDeps, false);

      if (updateSrc) updateTodo(hr->srcRelation, num);
      if (updateDst) updateTodo(hr->dstRelation, num);
      chcsToVisit.erase(num);
    }

    bool hasCycles()
    {
      if (cycles.size() > 0) return true;

      for (int i = 0; i < chcs.size(); i++)
        if (chcs[i].isFact) findCycles(i, vector<int>());

      assert (cycles.size() == prefixes.size());
      if (debug >= 3)
        for (int i = 0; i < cycles.size(); i++)
        {
          auto & c = prefixes[i];
          outs () << "      pref: ";
          for (auto & chcNum : c) outs () << *chcs[chcNum].srcRelation << " -> ";
          outs () << "    [";
          for (auto & chcNum : c) outs () << chcNum << " -> ";
          outs () << "]  ";
          auto & d = cycles[i];
          outs () << "      cycle: ";
          for (auto & chcNum : d) outs () << *chcs[chcNum].srcRelation << " -> ";
          outs () << "    [";
          for (auto & chcNum : d) outs () << chcNum << " -> ";
          outs () << "]\n";
        }
      return (cycles.size() > 0);
    }

    void findCycles(int chcNum, vector<int> vec)
    {
      Expr srcRel = chcs[chcNum].srcRelation;
      Expr dstRel = chcs[chcNum].dstRelation;
      bool res = false;
      for (int i = 0; i < vec.size(); i++)
      {
        auto c = vec[i];
        bool newCycle = (chcs[c].srcRelation == srcRel);
        // TODO: some cycles can be redundant
        if (newCycle)
        {
          cycles.push_back(vector<int>());
          prefixes.push_back(vector<int>());
          for (int j = 0; j < i; j++) prefixes.back().push_back(vec[j]);
          res = true;
        }
        if (res)
        {
          cycles.back().push_back(c);
        }
      }

      if (! res)
      {
        vec.push_back(chcNum);

        for (auto & i : outgs[dstRel])
        {
          if (chcs[i].dstRelation == failDecl) continue;
          bool newRel = true;
          for (auto & c : cycles)
          {
            if (c[0] == i)
            {
              newRel = false;
              break;
            }
          }
          if (newRel) findCycles(i, vec);
        }
      }
    }

    vector<int> empt;
    vector<int>& getCycleForRel(Expr rel)
    {
      for (auto & c : cycles)
        if (chcs[c[0]].srcRelation == rel)
          return c;
      return empt;
    }

    vector<int>& getCycleForRel(int chcNum)
    {
      return getCycleForRel(chcs[chcNum].srcRelation);
    }

    HornRuleExt* getFirstRuleOutside (Expr rel)
    {
      for (auto & c : cycles)
      {
        if (chcs[c[0]].srcRelation == rel)
        {
          for (auto & a : outgs[rel])
          {
            if (a != c.back()) return &chcs[a];
          }
        }
      }
      return NULL;
    }

    void addRule (HornRuleExt* r)
    {
      chcs.push_back(*r);
      Expr srcRel = r->srcRelation;
      if (!isOpX<TRUE>(srcRel))
      {
        if (invVars[srcRel].size() == 0)
        {
          addDeclAndVars(srcRel, r->srcVars);
        }
      }
      outgs[srcRel].push_back(chcs.size()-1);
    }

    void addDeclAndVars(Expr rel, ExprVector& args)
    {
      ExprVector types;
      for (auto &var: args) {
        types.push_back(bind::typeOf(var));
      }
      types.push_back(mk<BOOL_TY>(m_efac));

      decls.insert(bind::fdecl (rel, types));
      for (auto & v : args)
      {
        invVars[rel].push_back(v);
      }
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          errs () << "Multiple queries are unsupported\n";
          exit (1);
        }
      }
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      Expr tmp = keepQuantifiers(hr->body, hr->srcVars);
      return weakenForHardVars(tmp, hr->srcVars);
    }

    void wtoSort()
    {
      hasCycles();
      if (wtoCHCs.size() > 0)
      {
        outs () << "Already sorted\n";
        return;
      }

      int r1 = 0;

      for (auto & c : cycles)
      {
        unique_push_back(chcs[c[0]].srcRelation, wtoDecls);
        for (int i = 1; i < c.size(); i++)
        {
          unique_push_back(chcs[c[i]].dstRelation, wtoDecls);
          unique_push_back(&chcs[c[i]], wtoCHCs);
        }
      }

      int r2 = wtoDecls.size();
      if (r2 == 0) return;

      while (r1 != r2)
      {
        for (int i = r1; i < r2; i++)
        {
          auto dcl = wtoDecls[i];
          for (auto &hr : chcs)
          {
            if (find(wtoCHCs.begin(), wtoCHCs.end(), &hr) != wtoCHCs.end()) continue;

            if (hr.srcRelation == dcl)
            {
              unique_push_back(hr.dstRelation, wtoDecls);
              unique_push_back(&hr, wtoCHCs);
            }
            else if (hr.dstRelation == dcl)
            {
              unique_push_back(hr.srcRelation, wtoDecls);
              unique_push_back(&hr, wtoCHCs);
            }
          }
        }
        r1 = r2;
        r2 = wtoDecls.size();
      }

      assert(wtoCHCs.size() == chcs.size());

      // filter wtoDecls
      for (auto it = wtoDecls.begin(); it != wtoDecls.end();)
      {
        if (*it == failDecl || isOpX<TRUE>(*it)) it = wtoDecls.erase(it);
        else ++it;
      }
    }

    // Transformations

    void copyIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs) if (a.srcRelation == decl->left() && a.dstRelation == decl->left()) hr = &a;
      Expr pre = getPrecondition(hr);
      ExprSet newCnjs;
      newCnjs.insert(mk<NEG>(pre));
      for (int i = 0; i < hr->srcVars.size(); i++)
      {
        newCnjs.insert(mk<EQ>(hr->dstVars[i], hr->srcVars[i]));
      }
      Expr body2 = conjoin(newCnjs, m_efac);

      // adaping the code from BndExpl.hpp
      ExprVector ssa;
      ExprVector bindVars1;
      ExprVector bindVars2;
      ExprVector newLocals;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int c = 0; c < num; c++)
      {
        Expr body = hr->body;
        bindVars2.clear();
        if (c != 0)
        {
          body = replaceAll(mk<OR>(body, body2), hr->srcVars, bindVars1);
          for (int i = 0; i < hr->locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr->locVars[i], new_name);
            body = replaceAll(body, hr->locVars[i], var);
            newLocals.push_back(var);
          }
        }

        if (c != num-1)
        {
          for (int i = 0; i < hr->dstVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr->dstVars[i], new_name));
            body = replaceAll(body, hr->dstVars[i], bindVars2[i]);
            newLocals.push_back(bindVars2[i]);
          }
        }
        ssa.push_back(body);
        bindVars1 = bindVars2;
      }
      hr->body = conjoin(ssa, m_efac);
      hr->locVars.insert(hr->locVars.end(), newLocals.begin(), newLocals.end());
    }

    bool checkWithSpacer()
    {
      bool success = false;

      // fixed-point object
      ZFixedPoint<EZ3> fp (m_z3);
      ZParams<EZ3> params (m_z3);
      params.set (":engine", "spacer");
      params.set (":xform.slice", false);
      params.set (":pdr.utvpi", false);
      params.set (":use_heavy_mev", true);
      params.set (":xform.inline-linear", false);
      params.set (":xform.inline-eager", false);
      params.set (":xform.inline-eager", false);

      fp.set (params);

      fp.registerRelation (bind::boolConstDecl(failDecl));

      for (auto & dcl : decls) fp.registerRelation (dcl);
      Expr errApp;

      for (auto & r : chcs)
      {
        ExprSet allVars;
        allVars.insert(r.srcVars.begin(), r.srcVars.end());
        allVars.insert(r.dstVars.begin(), r.dstVars.end());
        allVars.insert(r.locVars.begin(), r.locVars.end());

        if (!r.isQuery)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.dstRelation)
            {
              r.head = bind::fapp (dcl, r.dstVars);
              break;
            }
          }
        }
        else
        {
          r.head = bind::fapp(bind::boolConstDecl(failDecl));
          errApp = r.head;
        }

        Expr pre;
        if (!r.isFact)
        {
          for (auto & dcl : decls)
          {
            if (dcl->left() == r.srcRelation)
            {
              pre = bind::fapp (dcl, r.srcVars);
              break;
            }
          }
        }
        else
        {
          pre = mk<TRUE>(m_efac);
        }

        fp.addRule(allVars, boolop::limp (mk<AND>(pre, r.body), r.head));
      }
      try {
        success = bool(!fp.query(errApp));
      } catch (z3::exception &e){
        char str[3000];
        strncpy(str, e.msg(), 300);
        errs() << "Z3 ex: " << str << "...\n";
        exit(55);
      }
      return success;
    }

    void print (bool full = false)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        auto & hr = chcs[i];
        if (full)
        {
          if (hr.isFact) outs() << "  INIT:\n";
          else if (hr.isInductive) outs() << "  TR:\n";
          else if (hr.isQuery) outs() << "  BAD:\n";
          else outs() << "  CHC:\n";
        }

        outs () << "    " << * hr.srcRelation;
        if (full && hr.srcVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.srcVars);
          outs () << "\b\b)";
        }
        else outs () << "[#" << hr.srcVars.size() << "]";
        outs () << " -> " << * hr.dstRelation;

        if (full && hr.dstVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.dstVars);
          outs () << "\b\b)";
        }
        else outs () << "[#" << hr.dstVars.size() << "]";
        if (full)
        {
          outs() << "\n    body: \n";
          if (treeSize(hr.body) < 1000)
            pprint(hr.body, 4);
          else outs () << " < . . . . too large . . . . >\n";
        }
        else outs() << "\n";
      }
    }
  };
}


#endif
