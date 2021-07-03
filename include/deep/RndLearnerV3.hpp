#ifndef RNDLEARNERV3__HPP__
#define RNDLEARNERV3__HPP__

#include "RndLearner.hpp"

#ifdef HAVE_ARMADILLO
#include "DataLearner.hpp"
#endif

using namespace std;
using namespace boost;
namespace ufo
{
  struct ArrAccessIter
  {
    bool grows;
    Expr iter;
    Expr qv;
    Expr precond;
    Expr range;
  };

  class RndLearnerV3 : public RndLearnerV2
  {
    private:

    ExprSet checked;
    set<HornRuleExt*> propped;
    map<int, ExprVector> candidates;
    map<int, deque<Expr>> deferredCandidates;
    int updCount = 1;
    bool boot = true;

    // extra options for disjunctive invariants
    unsigned dCandNum = 0;
    unsigned dAttNum = 100;
    unsigned dDepNum = 3;
    bool dAllMbp;
    bool dAddProp;
    bool dAddDat;
    bool dStrenMbp;

    map<int, Expr> postconds;
    map<int, Expr> ssas;
    map<int, Expr> prefs;

    map<int, vector<ArrAccessIter* >> qvits; // per cycle
    map<int, ExprSet> qvars;

    public:

    RndLearnerV3 (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned to, bool freqs, bool aggp,
                  bool _dAllMbp, bool _dAddProp, bool _dAddDat, bool _dStrenMbp) :
      RndLearnerV2 (efac, z3, r, to, freqs, aggp),
                  dAllMbp(_dAllMbp), dAddProp(_dAddProp), dAddDat(_dAddDat), dStrenMbp(_dStrenMbp) {}

    bool checkInit(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isFact && hr.dstRelation == rel)
        {
          adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    bool checkInductiveness(Expr rel)
    {
      vector<HornRuleExt*> adjacent;
      for (auto &hr: ruleManager.chcs)
      {
        bool checkedSrc = find(checked.begin(), checked.end(), hr.srcRelation) != checked.end();
        bool checkedDst = find(checked.begin(), checked.end(), hr.dstRelation) != checked.end();
        if ((hr.srcRelation == rel && hr.dstRelation == rel) ||
            (hr.srcRelation == rel && checkedDst) ||
            (hr.dstRelation == rel && checkedSrc) ||
            (checkedSrc && checkedDst) ||
            (hr.isFact && checkedDst))
        {
          if (!hr.isQuery) adjacent.push_back(&hr);
        }
      }
      if (adjacent.empty()) return true;
      return multiHoudini(adjacent);
    }

    ArrAccessIter* getQvit (int invNum, Expr it)
    {
      for (auto a : qvits[invNum]) if (a->qv == it) return a;
      return NULL;
    }

    Expr renameCand(Expr newCand, ExprVector& varsRenameFrom, int invNum)
    {
      for (auto & v : invarVars[invNum])
        newCand = replaceAll(newCand, varsRenameFrom[v.first], v.second);
      return newCand;
    }

    Expr eliminateQuantifiers(Expr e, ExprVector& varsRenameFrom, int invNum, bool bwd)
    {
      ExprSet complex;
      if (!containsOp<FORALL>(e))
      {
        e = rewriteSelectStore(e);
        findComplexNumerics(e, complex);
      }
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(varsRenameFrom.begin(), varsRenameFrom.end(), *it) != varsRenameFrom.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, varsRenameFrom);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = ufo::eliminateQuantifiers(eTmp, ev3);
      if (bwd) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(/*simplifyArithm*/(eTmp /*, false, true*/));
      e = replaceAll (eTmp, replsRev);
      e = renameCand(e, varsRenameFrom, invNum);
      return e;
    }

    void addPropagatedArrayCands(Expr rel, int invNum, Expr candToProp)
    {
      vector<int> tmp;
      ruleManager.getCycleForRel(rel, tmp);
      if (tmp.size() != 1) return; // todo: support

      Expr fls = candToProp->last()->right();
      for (auto & q : qvits[invNum])
        fls = replaceAll(fls, q->qv, q->iter);
      Expr bdy = rewriteSelectStore(ruleManager.chcs[tmp[0]].body);

      ExprVector ev;
      for (int h = 0; h < ruleManager.chcs[tmp[0]].dstVars.size(); h++)
      {
        Expr var = ruleManager.chcs[tmp[0]].srcVars[h];
        bool pushed = false;
        for (auto & q : qvits[invNum])
        {
          if (q->iter == var)
          {
            ev.push_back(var);
            pushed = true;
          }
        }
        if (!pushed) ev.push_back(ruleManager.chcs[tmp[0]].dstVars[h]);
      }

      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(fls, cnjs);
      getConj(bdy, cnjs);
      for (auto & a : cnjs) // hack
      {
        if (isOpX<EQ>(a) && !isNumeric(a->left())) continue;
        newCnjs.insert(a);
      }
      ExprMap mp;
      bdy = replaceSelects(conjoin(newCnjs, m_efac), mp);
      for (auto & a : mp)
      {
        if (!emptyIntersect(a.first, ruleManager.chcs[tmp[0]].dstVars))
        {
          ev.push_back(a.second);
        }
      }

      Expr newCand2;
      cnjs.clear();
      getConj(eliminateQuantifiers(bdy, ev, invNum, false), cnjs);
      for (auto & c : cnjs)
      {
        if (u.isTrue(c) || u.isFalse(c)) continue;
        Expr e = ineqNegReverter(c);
        if (isOp<ComparissonOp>(e))
        {
          for (auto & a : mp) e = replaceAll(e, a.second, a.first);
          for (auto & q : qvits[invNum])
          {
            if (containsOp<ARRAY_TY>(e) && !emptyIntersect(q->iter, e))
            {
              e = replaceAll(e, q->iter, q->qv);
              e = renameCand(e, ruleManager.chcs[tmp[0]].dstVars, invNum);

              // workaround: it works only during bootstrapping now
              arrCands[invNum].insert(e);
            }
          }
        }
      }
    }

    bool getCandForAdjacentRel(Expr candToProp, Expr constraint, Expr relFrom, ExprVector& varsRenameFrom, Expr rel, bool seed, bool fwd)
    {
      if (!containsOp<FORALL>(candToProp) && !u.isSat(candToProp, constraint))
        return false; // sometimes, maybe we should return true.

      int invNum = getVarIndex(rel, decls);
      int invNumFrom = getVarIndex(relFrom, decls);

      if (containsOp<FORALL>(candToProp))
      {
        // GF: not tested for backward propagation
        if (fwd == false) return true;
        if (finalizeArrCand(candToProp, constraint, relFrom))
        {
          assert (isOpX<FORALL>(candToProp));
          Expr qvar = getQvit(invNumFrom, bind::fapp(candToProp->arg(0)))->qv; // TODO: support nested loops with several qvars

          addPropagatedArrayCands(rel, invNum, candToProp);
          Expr newCand = getForallCnj(eliminateQuantifiers(
                        mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;

          auto candsTmp = candidates;
          candidates[invNum].push_back(newCand);

          bool res = checkCand(invNum, false) &&
                     propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
          if (!candidates[invNum].empty()) return res;

          for (auto & q : qvits[invNum])
          {
            Expr newCand1 = replaceAll(newCand, qvar->last(), q->qv->last());
            newCand1 = replaceArrRangeForIndCheck(invNum, newCand1, true);
            if (newCand1 == NULL) continue;
            candidates = candsTmp;
            candidates[invNum].push_back(newCand1);
            if (checkCand(invNum, false) &&
                propagateRec(rel, conjoin(candidates[invNum], m_efac), false))
              res = true;
          }
          return res;
        }
        else
        {
          // very ugly at the moment, to be revisited
          Expr newCand = getForallCnj(eliminateQuantifiers(
                          mk<AND>(candToProp, constraint), varsRenameFrom, invNum, false));
          if (newCand == NULL) return true;
          candidates[invNum].push_back(newCand);
          return checkCand(invNum, false) &&
               propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
        }
      }

      Expr newCand = eliminateQuantifiers(
                     (fwd ? mk<AND>(candToProp, constraint) :
                            mk<AND>(constraint, mkNeg(candToProp))),
                                    varsRenameFrom, invNum, !fwd);
      ExprSet cnjs;
      getConj(newCand, cnjs);
      addCandidates(rel, cnjs);

      if (seed)
      {
        if (u.isTrue(newCand)) return true;
        else return propagateRec(rel, newCand, true);
      }
      else
      {
        checkCand(invNum, false);
        return propagateRec(rel, conjoin(candidates[invNum], m_efac), false);
      }
    }

    bool addCandidate(int invNum, Expr cnd)
    {
      SamplFactory& sf = sfs[invNum].back();
      Expr allLemmas = sf.getAllLemmas();
      if (containsOp<FORALL>(cnd) || containsOp<FORALL>(allLemmas))
      {
        if (containsOp<FORALL>(cnd))
          cnd = replaceArrRangeForIndCheck (invNum, cnd);
        candidates[invNum].push_back(cnd);
        return true;
      }
      if (!isOpX<TRUE>(allLemmas) && u.implies(allLemmas, cnd)) return false;

      for (auto & a : candidates[invNum])
        if (a == cnd) return false;
      candidates[invNum].push_back(cnd);
      return true;
    }

    void addCandidates(Expr rel, ExprSet& cands)
    {
      int invNum = getVarIndex(rel, decls);
      for (auto & a : cands) addCandidate(invNum, a);
    }

    bool finalizeArrCand(Expr& cand, Expr constraint, Expr relFrom)
    {
      // only forward currently
      if (!isOpX<FORALL>(cand)) return false;
      if (!containsOp<ARRAY_TY>(cand)) return false;

      // need to make sure the candidate is finalized (i.e., not a nested loop)
      int invNum = getVarIndex(relFrom, decls);
      if (u.isSat(postconds[invNum], constraint)) return false;

      ExprSet cnj;
      for (int i = 0; i < cand->arity()-1; i++)
      {
        Expr qv = bind::fapp(cand->arg(i));
        auto q = getQvit(invNum, qv);
        getConj(q->range, cnj);
      }

      cand = replaceAll(cand, cand->last()->left(), conjoin(cnj, m_efac));
      return true;
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    Expr replaceArrRangeForIndCheck(int invNum, Expr cand, bool fwd = false)
    {
      assert(isOpX<FORALL>(cand));
      ExprSet cnjs;
      getConj(cand->last()->left(), cnjs);
      for (int i = 0; i < cand->arity()-1; i++)
      {
        auto qv = bind::fapp(cand->arg(i));
        auto str = getQvit(invNum, qv);
        Expr itRepl = str->iter;

        if (contains(cand->last()->right(), qv))
        {
          if      (str->grows && fwd)   cnjs.insert(mk<GEQ>(qv, itRepl));
          else if (str->grows && !fwd)  cnjs.insert(mk<LT>(qv, itRepl));
          else if (!str->grows && fwd)  cnjs.insert(mk<LEQ>(qv, itRepl));
          else if (!str->grows && !fwd) cnjs.insert(mk<GT>(qv, itRepl));
        }
        else
        {
          for (auto it = cnjs.begin(); it != cnjs.end(); )
          {
            if (contains (*it, qv)) it = cnjs.erase(it);
            else ++it;
          }
        }
        cand = replaceAll(cand, cand->last()->left(), conjoin(cnjs, m_efac));
      }
      return simplifyQuants(cand);
    }

    bool propagate(int invNum, Expr cand, bool seed) { return propagate(decls[invNum], cand, seed); }

    bool propagate(Expr rel, Expr cand, bool seed)
    {
      propped.clear();
      checked.clear();
      return propagateRec(rel, cand, seed);
    }

    bool propagateRec(Expr rel, Expr cand, bool seed)
    {
      bool res = true;
      checked.insert(rel);
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery || hr.isFact) continue;

        Expr constraint = hr.body;

        // forward:
        if (hr.srcRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          if (hr.isInductive && ruleManager.hasArrays[rel]) continue;     // temporary workarond
          propped.insert(&hr);
          SamplFactory* sf1 = &sfs[getVarIndex(hr.srcRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf1->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.srcVars);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.dstVars, hr.dstRelation, seed, true);
        }
        // backward (very similarly):
        if (hr.dstRelation == rel && find(propped.begin(), propped.end(), &hr) == propped.end())
        {
          propped.insert(&hr);
          SamplFactory* sf2 = &sfs[getVarIndex(hr.dstRelation, decls)].back();
          Expr replCand = replaceAllRev(cand, sf2->lf.nonlinVars);
          replCand = replaceAll(replCand, ruleManager.invVars[rel], hr.dstVars);
          res = res && getCandForAdjacentRel (replCand, constraint, rel, hr.srcVars, hr.srcRelation, seed, false);
        }
      }
      return res;
    }

    bool checkCand(int invNum, bool propa = true)
    {
      Expr rel = decls[invNum];
      if (!checkInit(rel)) return false;
      if (!checkInductiveness(rel)) return false;

      return !propa || propagate(invNum, conjoin(candidates[invNum], m_efac), false);
    }

    // a simple method to generate properties of a larger Array range, given already proven ranges
    void generalizeArrInvars (SamplFactory& sf)
    {
      if (sf.learnedExprs.size() > 1)
      {
        ExprVector posts;
        ExprVector pres;
        map<Expr, ExprVector> tmp;
        ExprVector tmpVars;
        ExprVector arrVars;
        Expr tmpIt = bind::intConst(mkTerm<string> ("_tmp_it", m_efac));

        for (auto & a : sf.learnedExprs)
        {
          if (!isOpX<FORALL>(a)) continue;
          Expr learnedQF = a->last();
          if (!isOpX<IMPL>(learnedQF)) continue;
          ExprVector se;
          filter (learnedQF->last(), bind::IsSelect (), inserter(se, se.begin()));

          // filter out accesses via non-quantified indeces
          for (auto it = se.begin(); it != se.end();)
          {
            bool found = false;
            for (int i = 0; i < a->arity(); i++)
            {
              if (contains(se[0]->right(), a->arg(0)))
              {
                found = true;
                break;
              }
            }
            if (!found) it = se.erase(it);
            else ++it;
          }

          bool multipleIndex = false;
          for (auto & s : se) {
            if (se[0]->right() != s->right()) {
              multipleIndex = true;
              break;
            }
          }

          if (se.size() == 0 || multipleIndex) continue;

          if (arrVars.size() == 0) {
            for (int index = 0; index < se.size(); index++) {
              arrVars.push_back(se[index]->left());
              tmpVars.push_back(bind::intConst(mkTerm<string> ("_tmp_var_" + lexical_cast<string>(index), m_efac)));
            }
          } else {
            bool toContinue = false;
            for (auto & s : se) {
              if (find(arrVars.begin(), arrVars.end(), s->left()) == arrVars.end()) {
                toContinue = true;
                break;
              }
            }
            if (toContinue) continue;
          }

          Expr postReplaced = learnedQF->right();
          for (int index = 0; index < se.size() && index < tmpVars.size(); index++)
          postReplaced = replaceAll(postReplaced, se[index], tmpVars[index]);

          ExprSet postVars;
          filter(postReplaced, bind::IsConst(), inserter(postVars, postVars.begin()));
          for (auto & fhVar : sf.lf.getVars()) postVars.erase(fhVar);
          for (auto & tmpVar : tmpVars) postVars.erase(tmpVar);
          if (postVars.size() > 0)
          {
            AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(postReplaced, mk<EQ>(tmpIt, se[0]->right())), postVars);
            if (ae.solve())
            {
              Expr pr = ae.getValidSubset();
              ExprSet conjs;
              getConj(pr, conjs);
              if (conjs.size() > 1)
              {
                for (auto conjItr = conjs.begin(); conjItr != conjs.end();)
                {
                  ExprVector conjVars;
                  filter (*conjItr, bind::IsConst(), inserter(conjVars, conjVars.begin()));
                  bool found = false;
                  for (auto & conjVar : conjVars)
                  {
                    if (find (tmpVars.begin(), tmpVars.end(), conjVar) != tmpVars.end())
                    {
                      found = true;
                      break;
                    }
                  }
                  if (!found) conjItr = conjs.erase(conjItr);
                  else ++conjItr;
                }
              }
              postReplaced = conjoin(conjs, m_efac);
            }
          }

          pres.push_back(learnedQF->left());
          posts.push_back(postReplaced);
          tmp[mk<AND>(learnedQF->left(), postReplaced)].push_back(se[0]->right());
        }

        if (tmp.size() > 0)
        {
          for (auto & a : tmp)
          {
            if (a.second.size() > 1)
            {
              Expr disjIts = mk<FALSE>(m_efac);
              for (auto & b : a.second) disjIts = mk<OR>(disjIts, mk<EQ>(tmpIt, b));
              ExprSet elementaryIts;
              filter (disjIts, bind::IsConst (), inserter(elementaryIts, elementaryIts.begin()));
              for (auto & a : sf.lf.getVars()) elementaryIts.erase(a);
              elementaryIts.erase(tmpIt);
              if (elementaryIts.size() == 1)
              {
                AeValSolver ae(mk<TRUE>(m_efac), mk<AND>(disjIts, a.first->left()), elementaryIts);
                if (ae.solve())
                {
                  ExprVector args;
                  Expr it = *elementaryIts.begin();
                  args.push_back(it->left());
                  Expr newPre = replaceAll(ae.getValidSubset(), tmpIt, it);
                  Expr newPost = replaceAll(a.first->right(), tmpIt, it);
                  for (int index = 0; index < tmpVars.size() && index < arrVars.size(); index++)
                  newPost = replaceAll(newPost, tmpVars[index], mk<SELECT>(arrVars[index], it));
                  args.push_back(mk<IMPL>(newPre, newPost));
                  Expr newCand = mknary<FORALL>(args);
                  sf.learnedExprs.insert(newCand);
                }
              }
            }
          }
        }
      }
    }

    void assignPrioritiesForLearned()
    {
//      bool progress = true;
      for (auto & cand : candidates)
      {
        if (cand.second.size() > 0)
        {
          ExprVector invVars;
          for (auto & a : invarVars[cand.first]) invVars.push_back(a.second);
          SamplFactory& sf = sfs[cand.first].back();
          for (auto b : cand.second)
          {
            b = simplifyArithm(b);
            if (containsOp<ARRAY_TY>(b) || findNonlin(b))
            {
              sf.learnedExprs.insert(b);
            }
            else
            {
              Expr learnedCand = normalizeDisj(b, invVars);
              Sampl& s = sf.exprToSampl(learnedCand);
              sf.assignPrioritiesForLearned();
              if (!u.implies(sf.getAllLemmas(), learnedCand))
                sf.learnedExprs.insert(learnedCand);
            }
//            else progress = false;
          }
        }
      }
//            if (progress) updateGrammars(); // GF: doesn't work great :(
    }

    Expr mkImplCnd(Expr pre, Expr cand)
    {
      if (isOpX<FORALL>(cand))
      {
        Expr tmp = cand->last()->right();
        return replaceAll(cand, tmp, mkImplCnd(pre, tmp));
      }
      return mk<IMPL>(pre, cand);
    }

    bool synthesizeDisjLemmas(int invNum, int cycleNum, Expr rel,
                              Expr cnd, Expr splitter, Expr ind, unsigned depth, Expr lastModel = NULL)
    {
      if (dCandNum++ == dAttNum || depth == dDepNum) return true;
      Expr invs = conjoin(sfs[invNum].back().learnedExprs, m_efac);

      if (isOpX<FORALL>(cnd)) cnd = replaceArrRangeForIndCheck (invNum, cnd);

      vector<int>& cycle = ruleManager.cycles[cycleNum];
      ExprVector& srcVars = ruleManager.chcs[cycle[0]].srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      Expr cndPrime = replaceAll(cnd, srcVars, dstVars);
      Expr cndSsa = mk<AND>(cnd, ssas[invNum]);
      Expr cndSsaPr = mk<AND>(cndSsa, cndPrime);

      ExprVector mbps;

      while (true)
      {
        Expr avail = mkNeg(disjoin(mbps, m_efac));
        Expr fla = mk<AND>(splitter, cndSsa);     // to weaken MBP further

        if (lastModel == NULL) {
          if (isOpX<TRUE>(splitter) && u.isSat(avail, prefs[invNum], cndSsaPr)) {
            fla = mk<AND>(prefs[invNum], cndSsaPr);
          } else if (u.isSat(avail, splitter, cndSsaPr)) {
            fla = mk<AND>(splitter, cndSsaPr);
          } else if (u.isSat(avail, splitter, cndSsa)) {
            fla = mk<AND>(splitter, cndSsa);
          } else break;

          lastModel = u.getModel();
        }

        if (lastModel == NULL) break;
        Expr mbp = u.getWeakerMBP(
                     keepQuantifiers (
                       u.getTrueLiterals(ssas[invNum], lastModel), srcVars), fla, srcVars);

        bool toadd = true;
        for (int j = 0; j < mbps.size(); j++)
          if (u.isSat(mbps[j], mbp))
          {
            mbps[j] = mk<OR>(mbps[j], mbp);
            toadd = false;
            break;
          }
        if (toadd) mbps.push_back(mbp);
        if (isOpX<FORALL>(cnd)) break;    // temporary workaround for arrays (z3 might fail in giving models)
        if (dAllMbp)
          lastModel = NULL;
        else
          break;
      }

      for (auto mbp : mbps)
      {
        if (!u.isSat(invs, mbp, splitter)) return true;

        if (dStrenMbp)
        {
          ExprSet tmp, tmp2;
          getConj(mbp, tmp);

          if (u.implies (prefs[invNum], cnd)) mutateHeuristic(prefs[invNum], tmp2);
          tmp2.insert(sfs[invNum].back().learnedExprs.begin(), sfs[invNum].back().learnedExprs.end());

          for (auto m : tmp)
          {
            if (!isOp<ComparissonOp>(m)) continue;
            for (auto t : tmp2)
            {
              if (!isOp<ComparissonOp>(t)) continue;
              Expr t1 = mergeIneqs(t, m);
              if (t1 == NULL) continue;
              t1 = simplifyArithm(t1);
              if (u.implies(mk<AND>(t1, ssas[invNum]), replaceAll(t1, srcVars, dstVars))) // && u.isSat(ind, t1))
                ind = mk<AND>(ind, t1);
            }
          }
        }

        if (u.isEquiv(mbp, splitter)) {
          candidates[invNum].push_back(mkImplCnd(mk<AND>(mbp, ind), cnd));
          candidates[invNum].push_back(mkImplCnd(mbp, cnd));
          return true;
        }

        Expr candImpl;
        if (isOpX<FORALL>(cnd))
        {
          Expr splitterArr = mk<AND>(splitter, mbp);
          for (auto & q : qvits[invNum])
            splitterArr = replaceAll(splitterArr, q->iter, q->qv);
          candImpl = mkImplCnd(splitterArr, cnd);
        }
        else
        {
          candImpl = mkImplCnd(mk<AND>(splitter, mbp), cnd); //mkImplCnd(mk<AND>(mk<AND>(splitter, ind), mbp), cnd);
          candidates[invNum].push_back(mkImplCnd(mk<AND>(splitter, ind), cnd)); // heuristic to add a candidate with weaker precond
          candidates[invNum].push_back(mkImplCnd(mk<AND>(mk<AND>(splitter, ind), mbp), cnd));
        }

        if (find(candidates[invNum].begin(), candidates[invNum].end(), candImpl) != candidates[invNum].end())
          return true;
        candidates[invNum].push_back(candImpl);

        map<Expr, ExprSet> cands;

        if (dAddProp)
        {
          ExprSet s;
          ExprVector vars = dstVars;
          if (isOpX<FORALL>(cnd))
          {
            s.insert(cnd->last());
            for (int i = 0; i < cnd->arity()-1; i++)
            {
              vars.push_back(bind::fapp(cnd->arg(i)));
            }
          }
          else
          {
            s.insert(cnd);
          }
          s.insert(mbp);
          s.insert(splitter);
          s.insert(ind);
          s.insert(ssas[invNum]);
          s.insert(mkNeg(replaceAll(mk<AND>(mk<AND>(splitter, ind), mbp), srcVars, dstVars)));
          Expr newCand = keepQuantifiers (conjoin(s, m_efac), dstVars);
          newCand = u.removeITE(replaceAll(newCand, dstVars, srcVars));
          if (isOpX<FORALL>(cnd))
          {
            cands[rel].insert(replaceAll(cnd, cnd->last(), newCand));
          }
          else
          {
            getConj(newCand, cands[rel]);
          }
        }

        Expr nextModel;
        ExprSet qfInvs, candsToDat, se;
        if (dAddDat)
        {
          getArrInds(ssas[invNum], se);
          if (isOpX<FORALL>(cnd))
            qfInvs.insert(cnd->right()->right());              // only the actual inv without the splitter/mbp
          else
            candsToDat.insert(candImpl);
            for (auto & inv : sfs[invNum].back().learnedExprs) // basically, invs
              if (isOpX<FORALL>(inv))
                qfInvs.insert(inv->right()->right());
              else
                candsToDat.insert(inv);
            for (auto & s : se)
            {
              Expr candToDat = conjoin(qfInvs, m_efac);
              for (auto & q : qvits[invNum])
                candToDat = replaceAll(candToDat, q->qv, s);
              candsToDat.insert(candToDat);
            }
          nextModel = getDataCandidates(cands, rel, mkNeg(mbp), conjoin(candsToDat, m_efac));
        }

        // postprocess behavioral arrCands
        if (!arrCands[invNum].empty())
        {
          for (auto &a : arrCands[invNum])
          {
            Expr arrCand = a;
            for (auto &q : qvits[invNum])
              arrCand = replaceAll(arrCand, q->iter, q->qv);
            if (find (qfInvs.begin(), qfInvs.end(), arrCand) == qfInvs.end())
              cands[rel].insert(sfs[invNum].back().af.getSimplCand(arrCand));
          }
          arrCands[invNum].clear();
        }

        for (auto & c : cands[rel])
        {
          if (c == cnd) continue;
          if(isOpX<FORALL>(cnd) && !isOpX<FORALL>(c)) continue;
          synthesizeDisjLemmas(invNum, cycleNum, rel, c, mk<AND>(splitter, mkNeg(mbp)), ind, depth + 1, nextModel);
          if (isOpX<FORALL>(cnd)) break;   // temporary workaround for arrays (z3 might fail in giving models)
        }
      }
      return true;
    }

    bool synthesize(unsigned maxAttempts, bool doDisj)
    {
      ExprSet cands;
      for (int i = 0; i < maxAttempts; i++)
      {
        // next cand (to be sampled)
        // TODO: find a smarter way to calculate; make parametrizable
        int cycleNum = i % ruleManager.cycles.size();
        int tmp = ruleManager.cycles[cycleNum][0];
        Expr rel = ruleManager.chcs[tmp].srcRelation;
        int invNum = getVarIndex(rel, decls);
        candidates.clear();
        SamplFactory& sf = sfs[invNum].back();
        Expr cand;
        if (deferredCandidates[invNum].empty())
          cand = sf.getFreshCandidate(i < 25);  // try simple array candidates first
        else {
          cand = deferredCandidates[invNum].back();
          deferredCandidates[invNum].pop_back();
        }
        if (cand != NULL && isOpX<FORALL>(cand) && isOpX<IMPL>(cand->last()))
        {
          if (!u.isSat(cand->last()->left())) cand = NULL;
        }
        if (cand == NULL) continue;
        if (printLog) outs () << " - - - sampled cand (#" << i << ") for " << *decls[invNum] << ": " << *cand << "\n";
        if (!addCandidate(invNum, cand)) continue;

        bool lemma_found = checkCand(invNum);
        if (doDisj && (isOp<ComparissonOp>(cand) || isOpX<FORALL>(cand)))
        {
          dCandNum = 0;
          lemma_found = synthesizeDisjLemmas(invNum, cycleNum, rel, cand, mk<TRUE>(m_efac), mk<TRUE>(m_efac), 0) &&
                        multiHoudini(ruleManager.wtoCHCs);
        }
        if (lemma_found)
        {
          assignPrioritiesForLearned();
          generalizeArrInvars(sf);
          if (checkAllLemmas())
          {
            outs () << "Success after " << (i+1) << " iterations "
                    << (deferredCandidates[invNum].empty() ? "(+ rnd)" : "") << "\n";
            printSolution();
            return true;
          }
        }
      }
      outs() << "unknown\n";
      return false;
    }

    bool filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          for (auto & hr : ruleManager.chcs)
          {
            if (hr.dstRelation == decls[i]) worklist.push_back(&hr);
          }
        }
      }

      // basically, just checks initiation and immediately removes bad candidates
      multiHoudini(worklist, false);

      for (int i = 0; i < invNumber; i++)
      {
        if (!u.isSat(candidates[i]))
        {
          ExprVector cur;
          deque<Expr> def;
          u.splitUnsatSets(candidates[i], cur, def);
          deferredCandidates[i] = def;
          candidates[i] = cur;
        }
      }

      return true;
    }

    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) return false;
      map<int, ExprVector> candidatesTmp = candidates;
      bool res1 = true;
      for (auto &h: worklist)
      {
        HornRuleExt& hr = *h;

        if (hr.isQuery) continue;

        boost::tribool b = checkCHC(hr, candidatesTmp);

        if (b || indeterminate(b))
        {
          bool res2 = true;
          int invNum = getVarIndex(hr.dstRelation, decls);

          Expr model = NULL;
          if (b) model = u.getModel(hr.dstVars);

          if (u.isModelSkippable(model, hr.dstVars, candidatesTmp))
          {
            // something went wrong with z3. do aggressive weakening (TODO: try bruteforce):
            // candidatesTmp[invNum].clear();
            candidatesTmp[invNum].pop_back();
            res2 = false;
          }
          else
          {
            ExprVector& ev = candidatesTmp[invNum];
            ExprVector invVars;
            for (auto & a : invarVars[invNum]) invVars.push_back(a.second);
            SamplFactory& sf = sfs[invNum].back();

            for (auto it = ev.begin(); it != ev.end(); )
            {
              Expr repl = *it;
              for (auto & v : invarVars[invNum]) repl = replaceAll(repl, v.second, hr.dstVars[v.first]);

              if (!u.isSat(model, repl))
              {
                if (hr.isFact)
                {
                  Expr failedCand = normalizeDisj(*it, invVars);
//                  outs () << "failed cand for " << *hr.dstRelation << ": " << *failedCand << "\n";
                  if (sf.initialized > 0)
                  {
                    Sampl& s = sf.exprToSampl(failedCand);
                    sf.assignPrioritiesForFailed();
                  }
                }
                if (boot)
                {
                  if (isOpX<EQ>(*it)) deferredCandidates[invNum].push_back(*it);  //  prioritize equalities
                  else deferredCandidates[invNum].push_front(*it);
                }
                it = ev.erase(it);
                res2 = false;
              }
              else
              {
                ++it;
              }
            }
          }

          if (recur && !res2)
          {
            res1 = false;
            break;
          }
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool findInvVar(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));

      for (auto & v : vars)
      {
        bool found = false;
        for (auto & w : invarVars[invNum])
        {
          if (w.second == v)
          {
            found = true;
            break;
          }
        }
        if (!found)
        {
          if (find (ve.begin(), ve.end(), v) == ve.end())
            return false;
        }
      }
      return true;
    }

    bool toCont(int invNum, Expr expr, ExprVector& ve)
    {
      ExprSet vars;
      filter (expr, bind::IsConst (), inserter(vars, vars.begin()));
      bool toCont = true;
      for (auto & expr : vars)
      {
        if (!findInvVar(invNum, expr, ve))
        {
          toCont = false;
          break;
        }
      }
      return toCont;
    }

    // adapted from doSeedMining
    void getSeeds(Expr invRel, map<Expr, ExprSet>& cands, bool analizeCode = true)
    {
      int invNum = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[invNum].back();
      ExprSet candsFromCode;
      bool analizedExtras = false;
      bool isFalse = false;
      bool hasArrays = false;

      // for Arrays
      ExprSet tmpArrAccess;
      ExprSet tmpArrSelects;
      ExprSet tmpArrCands;
      ExprSet tmpArrFuns;
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;
        SeedMiner sm (hr, invRel, invarVars[invNum], sf.lf.nonlinVars);

        if (analizeCode) sm.analizeCode();
        else sm.candidates.clear();
        if (!analizedExtras && hr.srcRelation == invRel)
        {
          sm.analizeExtras (cands[invRel]);
          analizedExtras = true;
        }
        for (auto &cand : sm.candidates) candsFromCode.insert(cand);

        // for arrays
        if (analizeCode && ruleManager.hasArrays[invRel])
        {
          tmpArrCands.insert(sm.arrCands.begin(), sm.arrCands.end());
          tmpArrSelects.insert(sm.arrSelects.begin(), sm.arrSelects.end());
          tmpArrFuns.insert(sm.arrFs.begin(), sm.arrFs.end());
          hasArrays = true;
        }
      }

      if (hasArrays)
      {

        for (int qNum = 0; qNum < qvits[invNum].size(); qNum++)
        {
          auto & q = qvits[invNum][qNum];
          Expr pre = q->precond;
          Expr qVar = bind::intConst(mkTerm<string>("_FH_arr_it_" + lexical_cast<string>(qNum), m_efac));
          q->qv = qVar;
          arrAccessVars[invNum].push_back(qVar);

          assert (isOpX<EQ>(pre)); // TODO: support more

          ExprVector invAndIterVarsAll;
          for (auto & a : invarVars[invNum]) invAndIterVarsAll.push_back(a.second);
          invAndIterVarsAll.push_back(qVar);

          Expr fla = (q->grows) ? mk<GEQ>(qVar, pre->right()) :
                                  mk<LEQ>(qVar, pre->right());

          ExprSet tmp;
          getConj(postconds[invNum], tmp);
          for (auto it = tmp.begin(); it != tmp.end(); )
            if (contains(*it, q->iter)) ++it; else it = tmp.erase(it);

          q->range = normalizeDisj(mk<AND>(fla,
                     replaceAll(conjoin(tmp, m_efac), q->iter, qVar)), invAndIterVarsAll);
          arrIterRanges[invNum].insert(q->range);

          // repair behavioral arrCands
          if (!arrCands[invNum].empty())
          {
            ExprSet repCands;
            for (auto & a : arrCands[invNum])
              repCands.insert(replaceAll(a, q->iter, qVar));
            arrCands[invNum] = repCands;
          }
        }

        // TODO: revisit handling of nested loops
        /*
        auto nested = ruleManager.getNestedRel(invRel);
        if (nested != NULL)
        {
          int invNumTo = getVarIndex(nested->dstRelation, decls);
          // only one variable for now. TBD: find if we need more
          Expr qVar2 = bind::intConst(mkTerm<string> ("_FH_nst_it", m_efac));
          arrAccessVars[invNum].push_back(qVar2);

          Expr range = conjoin (arrIterRanges[invNumTo], m_efac);
          ExprSet quantified;
          for (int i = 0; i < nested->dstVars.size(); i++)
          {
            range = replaceAll(range, invarVars[invNumTo][i], nested->dstVars[i]);
            quantified.insert(nested->dstVars[i]);
          }

          // naive propagation of ranges
          ExprSet cnjs;
          getConj(nested->body, cnjs);
          for (auto & a : cnjs)
          {
            for (auto & b : quantified)
            {
              if (isOpX<EQ>(a) && a->right() == b)
              {
                range = replaceAll(range, b, a->left());
              }
              else if (isOpX<EQ>(a) && a->left() == b)
              {
                range = replaceAll(range, b, a->right());
              }
            }
          }
          arrIterRanges[invNum].insert(
                replaceAll(replaceAll(range, *arrAccessVars[invNumTo].begin(), qVar2),
                      q->iter, *arrAccessVars[invNum].begin()));
        }
         */

        // process all quantified seeds
        for (auto & a : tmpArrCands)
        {
          if (u.isTrue(a) || u.isFalse(a)) continue;
          Expr replCand = replaceAllRev(a, sf.lf.nonlinVars);
          ExprSet allVars;
          getExtraVars(replCand, ruleManager.invVars[invRel], allVars);
          if (allVars.size() < 2 &&
              !u.isTrue(replCand) && !u.isFalse(replCand))
          {
            if (allVars.size() == 0)
            {
              candsFromCode.insert(replCand);
              for (auto & q : qvits[invNum])
                replCand = replaceAll(replCand, q->iter, q->qv);
              arrCands[invNum].insert(replCand);
            }
            else
              for (auto & q : qvits[invNum])
                if (typeOf(*allVars.begin()) == typeOf(q->qv))
                  arrCands[invNum].insert(replaceAll(replCand, *allVars.begin(), q->qv));
          }
        }

        // trick for tiling benchs
        ExprSet afs;
        for (auto & a : tmpArrFuns)
        {
          ExprVector vars;
          filter (a, bind::IsConst(), std::inserter (vars, vars.begin ()));
          if (vars.size() != 1 || *vars.begin() == a) continue;
          afs.insert(replaceAll(a, *vars.begin(), arrAccessVars[invNum][0]));
        }

//        for (auto & s : afs)
//        {
//          for (auto & qcand : arrCands[invNum])
//          {
//            outs () << "  qcand: " << *qcand << "\n";
//            ExprSet se;
//            filter (qcand, bind::IsSelect (), inserter(se, se.begin()));
//            for (auto & arrsel : se)
//            {
//              Expr qcandTmp = replaceAll(qcand, arrsel->right(), s);
//              arrCands[invNum].insert(qcandTmp);
//              outs () << "   prepro: " << *qcandTmp << "\n";
//            }
//          }
//        }
      }
      // process all quantifier-free seeds
      for (auto & cand : candsFromCode)
      {
        Expr replCand = replaceAllRev(cand, sf.lf.nonlinVars);
        // sanity check for replCand:
        if (toCont (invNum, replCand, arrAccessVars[invNum]) && addCandidate(invNum, replCand))
          propagate (invNum, replCand, true);
      }
    }

    void refreshCands(map<Expr, ExprSet>& cands)
    {
      cands.clear();
      for (auto & a : candidates)
      {
        cands[decls[a.first]].insert(a.second.begin(), a.second.end());
      }
    }

    bool anyProgress(vector<HornRuleExt*> worklist)
    {
      for (int i = 0; i < invNumber; i++)
        // subsumption check
        for (auto & hr : worklist)
          if (hr->srcRelation == decls[i] || hr->dstRelation == decls[i])
            if (candidates[i].size() > 0)
              if (!u.implies (conjoin(sfs[i].back().learnedExprs, m_efac),
                conjoin(candidates[i], m_efac)))
                  return true;
      return false;
    }

    Expr getDataCandidates(map<Expr, ExprSet>& cands, Expr srcRel = NULL,
                           Expr splitter = NULL, Expr invs = NULL){
      Expr model;     // for splitters
#ifdef HAVE_ARMADILLO
      DataLearner dl(ruleManager, m_z3);
      if (srcRel == NULL || splitter == NULL) dl.computeData();
      for (auto & dcl : decls) {
        int invNum = getVarIndex(dcl, decls);
        ExprSet poly;
        if (srcRel == dcl && splitter != NULL)
          dl.computeData(srcRel, splitter, invs);
        dl.computePolynomials(dcl, poly);
        if (splitter != NULL)
          for (auto & a : dl.getConcrInvs(dcl)) cands[dcl].insert(a);
        if (srcRel == dcl && splitter != NULL)
          model = conjoin(dl.getConcrInvs(srcRel), m_efac);

        if (ruleManager.hasArrays[dcl])   // heuristic to remove cands irrelevant to counters and arrays
        {
          for (auto it = poly.begin(); it != poly.end();)
            for (auto q : qvits[invNum])
              if (emptyIntersect(q->iter, simplifyArithm(*it) ))
                it = poly.erase(it);
              else
                ++it;
        }
        mutateHeuristicEq(poly, cands[dcl], dcl, (splitter == NULL));
      }
#else
      outs() << "Skipping learning from data as required library (armadillo) not found\n";
#endif
      return model;
    }

    void mutateHeuristicEq(ExprSet& src, ExprSet& dst, Expr dcl, bool toProp)
    {
        int invNum = getVarIndex(dcl, decls);
        ExprSet src2;
        map<Expr, ExprVector> substs;
        // create various combinations:
        for (auto a1 = src.begin(); a1 != src.end(); ++a1)
        {
          if (!isOpX<EQ>(*a1) || !isNumeric((*a1)->left())) continue;

          for (auto a2 = std::next(a1); a2 != src.end(); ++a2)
          {
            if (!isOpX<EQ>(*a2) || !isNumeric((*a2)->left())) continue;
            src2.insert(mk<EQ>(mk<PLUS>((*a1)->left(), (*a2)->left()),
                                         mk<PLUS>((*a1)->right(), (*a2)->right())));
            src2.insert(mk<EQ>(mk<MINUS>((*a1)->left(), (*a2)->left()),
                                         mk<MINUS>((*a1)->right(), (*a2)->right())));
            src2.insert(mk<EQ>(mk<PLUS>((*a1)->left(), (*a2)->right()),
                                         mk<PLUS>((*a1)->right(), (*a2)->left())));
            src2.insert(mk<EQ>(mk<MINUS>((*a1)->left(), (*a2)->right()),
                                         mk<MINUS>((*a1)->right(), (*a2)->left())));
          }
        }

        for (auto a : src)
        {
          if (!isOpX<EQ>(a) || !isNumeric(a->left())) continue;
          // before pushing them to the cand set, we do some small mutations to get rid of specific consts
          a = simplifyArithm(normalize(a));
          if (isOpX<EQ>(a) && isIntConst(a->left()) &&
              isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
            substs[a->right()].push_back(a->left());
          src2.insert(a);
        }

        for (auto a : src2)
        {
          if (!u.isSat(mk<NEG>(a))) continue;
          a = simplifyArithm(normalize(a));
          if (printLog) outs () << "CAND FROM DATA: " << *a << "\n";

          if (toProp) propagate(dcl, a, true);

          if (containsOp<ARRAY_TY>(a))
            arrCands[invNum].insert(a);
          else
            u.insertUnique(a, dst);
          if (isNumericConst(a->right()))
          {
            cpp_int i1 = lexical_cast<cpp_int>(a->right());
            for (auto b : substs)
            {
              cpp_int i2 = lexical_cast<cpp_int>(b.first);

              if (i1 % i2 == 0 && i1/i2 != 0)
                for (auto c : b.second)
                {
                  Expr e = simplifyArithm(normalize(mk<EQ>(a->left(), mk<MULT>(mkMPZ(i1/i2, m_efac), c))));
                  if (!u.isSat(mk<NEG>(e))) continue;
                  if (containsOp<ARRAY_TY>(e))
                    arrCands[invNum].insert(e);
                  else
                    u.insertUnique(e, dst);
                  if (printLog) outs () << "CAND FROM DATA: " << *e << "\n";
                }
            }
          }
        }
    }

    bool bootstrap(bool doDisj)
    {
      filterUnsat();

      if (multiHoudini(ruleManager.wtoCHCs))
      {
        assignPrioritiesForLearned();
        if (checkAllLemmas())
        {
          outs () << "Success after bootstrapping\n";
          printSolution();
          return true;
        }
      }

      if (!doDisj) simplifyLemmas();
      boot = false;

      // try array candidates one-by-one (adapted from `synthesize`)
      // TODO: batching
//      if (ruleManager.hasArrays)
      {
        for (auto & dcl: ruleManager.wtoDecls)
        {
          int invNum = getVarIndex(dcl, decls);
          SamplFactory& sf = sfs[invNum].back();
          for (auto it = arrCands[invNum].begin(); it != arrCands[invNum].end();
               it = arrCands[invNum].erase(it))
          {
            Expr c = *it;
            if (u.isTrue(c) || u.isFalse(c)) continue;

            Expr cand = sf.af.getSimplCand(c);
            if (printLog) outs () << "- - - bootstrapped cand for " << *dcl << ": " << *cand << "\n";

            auto candidatesTmp = candidates[invNum]; // save for later
            if (!addCandidate(invNum, cand)) continue;
            if (checkCand(invNum))
            {
              assignPrioritiesForLearned();
              generalizeArrInvars(sf);
              if (checkAllLemmas())
              {
                outs () << "Success after bootstrapping\n";
                printSolution();
                return true;
              }
            }
            else
            {
              if (isOpX<EQ>(c))         // prioritize equality cands
                deferredCandidates[invNum].push_back(cand);
              else
                deferredCandidates[invNum].push_front(cand);
              if (candidates[invNum].empty()) candidates[invNum] = candidatesTmp;
            }
          }
        }

        // second round of bootstrapping (to be removed after Houdini supports arrays)

        candidates.clear();
        ExprVector empt;
        for (auto &hr: ruleManager.chcs)
        {
          if (hr.isQuery)
          {
            int invNum = getVarIndex(hr.srcRelation, decls);
            ExprSet cnjs;
            getConj(hr.body, cnjs);
            for (auto & a : cnjs)
            {
              if (isOpX<NEG>(a) && findInvVar(invNum, a, empt))
              {
                candidates[invNum].push_back(a->left());
                break;
              }
            }
            break;
          }
        }
        if (multiHoudini(ruleManager.wtoCHCs))
        {
          assignPrioritiesForLearned();
          if (checkAllLemmas())
          {
            outs () << "Success after bootstrapping\n";
            printSolution();
            return true;
          }
        }
      }

      return false;
    }

    void updateGrammars()
    {
      // convert candidates to curCandidates and run the method from RndLearner
      for (int ind = 0; ind < invNumber; ind++)
      {
        if (candidates[ind].size() == 0) curCandidates[ind] = mk<TRUE>(m_efac);
        else curCandidates[ind] = conjoin(candidates[ind], m_efac);
      }
      updateRels();
      updCount++;
    }

    bool checkAllLemmas()
    {
      candidates.clear();
      for (int i = ruleManager.wtoCHCs.size() - 1; i >= 0; i--)
      {
        auto & hr = *ruleManager.wtoCHCs[i];
        boost::tribool b = checkCHC(hr, candidates);
        if (b) {
          if (!hr.isQuery)
          {
            outs() << "WARNING: Something went wrong" <<
              (ruleManager.hasArrays[hr.srcRelation] || ruleManager.hasArrays[hr.dstRelation] ?
              " (possibly, due to quantifiers)" : "") <<
              ". Restarting...\n";

            for (int i = 0; i < decls.size(); i++)
            {
              SamplFactory& sf = sfs[i].back();
              ExprSet lms = sf.learnedExprs;
              for (auto & l : lms) candidates[i].push_back(l);
              sf.learnedExprs.clear();
            }
            multiHoudini(ruleManager.wtoCHCs);
            assignPrioritiesForLearned();

            return false;
            assert(0);    // only queries are allowed to fail
          }
          else
            return false; // TODO: use this fact somehow
        }
        else if (indeterminate(b)) return false;
      }
      return true;
    }

    boost::tribool checkCHC (HornRuleExt& hr, map<int, ExprVector>& annotations)
    {
      ExprSet exprs;
      exprs.insert(hr.body);

      if (!hr.isFact)
      {
        int invNum = getVarIndex(hr.srcRelation, decls);
        SamplFactory& sf = sfs[invNum].back();
        ExprSet lms = sf.learnedExprs;
        for (auto & a : annotations[invNum]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[invNum]) a = replaceAll(a, v.second, hr.srcVars[v.first]);
          exprs.insert(a);
        }
      }

      if (!hr.isQuery)
      {
        int invNum = getVarIndex(hr.dstRelation, decls);
        SamplFactory& sf = sfs[invNum].back();
        ExprSet lms = sf.learnedExprs;
        ExprSet negged;
        for (auto & a : annotations[invNum]) lms.insert(a);
        for (auto a : lms)
        {
          for (auto & v : invarVars[invNum]) a = replaceAll(a, v.second, hr.dstVars[v.first]);
          negged.insert(mkNeg(a));
        }
        exprs.insert(disjoin(negged, m_efac));
      }
      return u.isSat(exprs);
    }

    // it used to be called initArrayStuff, but now it does more stuff than just for arrays
    void initializeAux(BndExpl& bnd, int cycleNum, Expr pref)
    {
      vector<int>& cycle = ruleManager.cycles[cycleNum];
      HornRuleExt* hr = &ruleManager.chcs[cycle[0]];
      Expr rel = hr->srcRelation;
      ExprVector& srcVars = hr->srcVars;
      ExprVector& dstVars = ruleManager.chcs[cycle.back()].dstVars;
      assert(srcVars.size() == dstVars.size());

      int invNum = getVarIndex(rel, decls);

      prefs[invNum] = pref;
      Expr e = bnd.toExpr(cycle);
      ssas[invNum] = replaceAll(e, bnd.bindVars.back(), dstVars);

      if (qvits[invNum].size() > 0) return;

      ExprSet ssa;
      if (!containsOp<ARRAY_TY>(ssas[invNum])) return; // todo: support

      getConj(ssas[invNum], ssa);

      filter (ssas[invNum], bind::IsConst (), inserter(qvars[invNum], qvars[invNum].begin()));
      postconds[invNum] = ruleManager.getPrecondition(hr);

      for (int i = 0; i < dstVars.size(); i++)
      {
        Expr a = srcVars[i];
        Expr b = dstVars[i];
        if (!bind::isIntConst(a) /*|| !contains(postconds[invNum], a)*/) continue;

        bool implDecr = (bool)u.implies(ssas[invNum], mk<GT>(a, b));
        bool implGrow = !implDecr && (bool)u.implies(ssas[invNum], mk<LT>(a, b));
        if (implDecr || implGrow)
        {
          ArrAccessIter* ar = new ArrAccessIter();
          ar->iter = a;
          ar->grows = implGrow;
          qvits[invNum].push_back(ar);
          ruleManager.iterators[rel].push_back(i);
        }
      }

      ssa.clear();
      getConj(pref, ssa);
      for (auto & a : ssa)
      {
        for (auto & q : qvits[invNum])
        {
          if (contains(a, q->iter) && isOpX<EQ>(a))
          {
            q->precond = ineqSimplifier(q->iter, a);
            assert (q->precond->left() == q->iter);
            break;
          }
        }
      }

      if (!qvits[invNum].empty()) ruleManager.hasArrays[rel] = true;

      if (printLog)
      {
        outs () << "in total " << qvits[invNum].size() << " iters for " << *rel << ":\n";
        for (auto & q : qvits[invNum])
        {
          outs () << "      " << *q->iter
                  << "      " << q->grows
                  << "      " << *q->precond << "\n";
        }
      }
    }

    void simplifyLemmas()
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        u.removeRedundantConjuncts(sf.learnedExprs);
      }
    }

    void printSolution(bool simplify = true)
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        ExprSet lms = sf.learnedExprs;
        outs () << "(define-fun " << *rel << " (";
        for (auto & b : ruleManager.invVars[rel])
          outs () << "(" << *b << " " << u.varType(b) << ")";
        outs () << ") Bool\n  ";
        Expr tmp = conjoin(lms, m_efac);
        if (simplify && !containsOp<FORALL>(tmp)) u.removeRedundantConjuncts(lms);
        Expr res = simplifyArithm(conjoin(lms, m_efac));
        u.print(res);
        outs () << ")\n";
        assert(hasOnlyVars(res, ruleManager.invVars[rel]));
      }
    }
  };

  inline void learnInvariants3(string smt, unsigned maxAttempts, unsigned to, bool freqs, bool aggp,
                               bool enableDataLearning, bool doElim, bool doDisj,
                               bool dAllMbp, bool dAddProp, bool dAddDat, bool dStrenMbp)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt, doElim);
    BndExpl bnd(ruleManager);
    if (!ruleManager.hasCycles())
    {
      bnd.exploreTraces(1, ruleManager.chcs.size(), true);
      return;
    }

    RndLearnerV3 ds(m_efac, z3, ruleManager, to, freqs, aggp, dAllMbp, dAddProp, dAddDat, dStrenMbp);
    map<Expr, ExprSet> cands;
    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl);
    for (int i = 0; i < ruleManager.cycles.size(); i++)
    {
      Expr pref = bnd.compactPrefix(i);
      Expr rel = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
      ExprSet tmp;
      getConj(pref, tmp);
      for (auto & t : tmp)
        if (hasOnlyVars(t, ruleManager.invVars[rel]))
          cands[rel].insert(t);
      ds.mutateHeuristicEq(cands[rel], cands[rel], rel, true);
      ds.initializeAux(bnd, i, pref);
    }
    if (enableDataLearning) ds.getDataCandidates(cands);
    for (auto& dcl: ruleManager.wtoDecls) ds.addCandidates(dcl, cands[dcl]);
    for (auto& dcl: ruleManager.wtoDecls) ds.getSeeds(dcl, cands);
    ds.refreshCands(cands);
    for (auto& dcl: ruleManager.decls) ds.doSeedMining(dcl->arg(0), cands[dcl->arg(0)], false);
    ds.calculateStatistics();
    if (ds.bootstrap(doDisj)) return;
    std::srand(std::time(0));
    ds.synthesize(maxAttempts, doDisj);
  }
}

#endif