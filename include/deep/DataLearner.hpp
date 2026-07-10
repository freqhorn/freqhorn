#ifndef DATALEARNER__HPP__
#define DATALEARNER__HPP__

// currently only polynomials upto degree 2 is supported

#include <cstdlib>
#include <cstdio>
#include <fstream>
#include <vector>
#include <climits>
#include <ctime>
#include <cmath>
#include <algorithm>

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/vector.hpp>

#include "Horn.hpp"
#include "BndExpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  const double approxEqualTol = 0.001;
  const char approxEqualMethod[] = "absdiff";

  enum loglevel {NONE, ERROR, INFO, DEBUG};

  unsigned int LOG_LEVEL = INFO;

  template <typename T>
  void printmsg(T t)
  {
    std::cout << t << std::endl;
  }

  template <typename T, typename... Args>
  void printmsg(T t, Args... args)
  {
    std::cout << t << " ";
    printmsg(args...);
  }

  template <typename... Args>
  void printmsg(loglevel level, Args... args)
  {
    if (level <= LOG_LEVEL) {
      printmsg(args...);
    }
  }

  namespace ublas = boost::numeric::ublas;
  using Matrix = ublas::matrix<double>;
  using Vector = ublas::vector<double>;

  inline bool approxEqual(double lhs, double rhs)
  {
    return std::fabs(lhs - rhs) < approxEqualTol;
  }

  inline void fillMatrix(Matrix &m, double value)
  {
    for (unsigned int row = 0; row < m.size1(); row++)
      for (unsigned int col = 0; col < m.size2(); col++)
        m(row, col) = value;
  }

  inline void swapRows(Matrix &m, unsigned int lhs, unsigned int rhs)
  {
    if (lhs == rhs) return;
    for (unsigned int col = 0; col < m.size2(); col++)
      std::swap(m(lhs, col), m(rhs, col));
  }

  inline Vector getColumn(const Matrix &m, unsigned int col)
  {
    Vector result(m.size1());
    for (unsigned int row = 0; row < m.size1(); row++)
      result(row) = m(row, col);
    return result;
  }

  inline bool columnsApproxEqual(const Matrix &lhs, unsigned int lhsCol,
                                 const Matrix &rhs, unsigned int rhsCol)
  {
    if (lhs.size1() != rhs.size1()) return false;
    for (unsigned int row = 0; row < lhs.size1(); row++)
      if (!approxEqual(lhs(row, lhsCol), rhs(row, rhsCol))) return false;
    return true;
  }

  inline void appendColumn(Matrix &m, const Vector &col)
  {
    if (m.size1() == 0 && m.size2() == 0) {
      m.resize(col.size(), 1, false);
      for (unsigned int row = 0; row < col.size(); row++)
        m(row, 0) = col(row);
      return;
    }

    Matrix result(m.size1(), m.size2() + 1);
    for (unsigned int row = 0; row < m.size1(); row++) {
      for (unsigned int c = 0; c < m.size2(); c++)
        result(row, c) = m(row, c);
      result(row, m.size2()) = col(row);
    }
    m = result;
  }

  inline void shedColumn(Matrix &m, unsigned int removeCol)
  {
    if (m.size2() == 0 || removeCol >= m.size2()) return;

    Matrix result(m.size1(), m.size2() - 1);
    for (unsigned int row = 0; row < m.size1(); row++) {
      unsigned int dst = 0;
      for (unsigned int col = 0; col < m.size2(); col++)
        if (col != removeCol)
          result(row, dst++) = m(row, col);
    }
    m = result;
  }

  class DataLearner
  {

  private:

    CHCs& ruleManager;
    BndExpl bnd;
    ExprFactory &m_efac;
    unsigned int curPolyDegree;

    Matrix
    computeMonomial(const Matrix &dataMatrix)
    {
      Matrix monomialMatrix;
      if (curPolyDegree == 1) {
        monomialMatrix.resize(dataMatrix.size1(), dataMatrix.size2(), false);
        for (unsigned int i = 0; i < dataMatrix.size1(); i++) {
          for (unsigned int j = 0; j < dataMatrix.size2(); j++) {
            monomialMatrix(i,j) = dataMatrix(i,j);
          }
        }
      } else {
        //compute all monomials upto degree 2
        monomialMatrix.resize(dataMatrix.size1(), (dataMatrix.size2() * (dataMatrix.size2()+1)) / 2, false);
        for (unsigned int i = 0; i < dataMatrix.size1(); i++) {
          for(unsigned int j = 0, dmcol=0; j < dataMatrix.size2(); j++) {
            for (unsigned int k = j; k < dataMatrix.size2(); k++, dmcol++) {
              monomialMatrix(i, dmcol) = dataMatrix(i,j) * dataMatrix(i, k);
            }
          }
        }
      }

      return monomialMatrix;
    }

    Matrix
    gaussjordan(Matrix input)
    {
      if (input.size1() == 0 || input.size2() == 0)
        return Matrix(input.size2(), 0);

      unsigned int cur_row = 0;
      unsigned int cur_col = 0;
      const unsigned int UNDEFINED_PIVOT = 100;
      std::vector<unsigned int> rowToPivot(input.size1(), UNDEFINED_PIVOT);

      printmsg(DEBUG, "Before row: ", input.size1(), "x", input.size2());

      //row echleon form
      while (cur_col < input.size2() && cur_row < input.size1()) {

        if (input(cur_row, cur_col) == 0) {
          unsigned int next_nonzero;
          for (next_nonzero = cur_row; next_nonzero < input.size1(); next_nonzero++) {
            if (input(next_nonzero, cur_col) != 0) {
              break;
            }
          }
          if (next_nonzero == input.size1()) {
            cur_col++;
            continue;
          } else {
            swapRows(input, cur_row, next_nonzero);
          }
        }

        if (input(cur_row, cur_col) != 1) {
          double inverse = 1/input(cur_row, cur_col);
          for (unsigned int k = cur_col; k < input.size2(); k++) {
            input(cur_row, k) = input(cur_row,k)*inverse;
          }
        }

        for (unsigned int j = cur_row+1; j < input.size1(); j++) {
          double f = input(j, cur_col)/input(cur_row, cur_col);
          for (unsigned int k = 0; k < input.size2(); k++) {
            input(j,k) = input(j,k) - input(cur_row, k)*f;
          }
          input(j,cur_col) = 0;
        }

        rowToPivot[cur_row] = cur_col;

        cur_col++;
        cur_row++;
      }

      rowToPivot[input.size1()-1] = input.size2()-1;

      //reduced row echloen form
      if (cur_row != input.size1()) {
        //we have found a zero row before we reached last row
        cur_row = cur_row-1;
      } else {
        cur_row = input.size1()-1;
      }

      cur_col = rowToPivot[cur_row];

      while (cur_row < input.size1()) {

        cur_col = rowToPivot[cur_row];

        if (cur_col == UNDEFINED_PIVOT || input(cur_row,cur_col) == 0) {
          cur_row--;
          continue;
        }

        for (unsigned int j = cur_row-1; j < input.size1(); j--) {
          double f = input(j,cur_col)/input(cur_row,cur_col);
          for (unsigned int k = 0; k < input.size2(); k++) {
            input(j,k) = input(j,k) - input(cur_row,k)*f;
          }
        }
        cur_row--;
      }

      //      printmsg(INFO, "after row reduced\n", input);

      std::vector<unsigned int> independentVars;

      for (unsigned col = 0; col < input.size2(); col++) {
        if (col < input.size1() && input(col, col) == 0) {
          independentVars.push_back(col);
        }
      }

      Matrix basis(input.size2(), independentVars.size());
      fillMatrix(basis, 0);
      unsigned int basis_col = 0;

      for (auto indVar : independentVars) {
        for (unsigned int row = 0; row < input.size1(); row++) {
          if (rowToPivot[row] == UNDEFINED_PIVOT) {
            continue;
          }
          //TODO: replace -2 with lcm of column
          //printmsg(DEBUG, input(row,indVar), row, indVar);
          basis(rowToPivot[row], basis_col) = -1*input(row, indVar);
        }
        basis(indVar,basis_col)=1;
        basis_col++;
      }

      return basis;
    }

    void
    computetime(const string & msg, clock_t & start)
    {
      printmsg(DEBUG, msg, (clock() - start)/(CLOCKS_PER_SEC/1000.0));
      start = clock();
    }

    int
    algExprFromBasis(const Matrix & basis, vector<Expr> & polynomials, map<unsigned int, Expr>& monomialToExpr)
    {

      /*TODO: fix this; not working for 8.c*/
      // if (allNonZero(basis)) {
      // 	return 1;
      // }

      // create equations of the form a_1*x_1 + a_2*x_2 + ... = 0
      // where a_1, a_2, etc are from basis columns values
      // and x_1, x_2 etc are monomials from corresponding basis' rows
      // to disallow unsound invariants like a_1 = 0 add only candidates with atleast two terms
      Expr zero = mkTerm(mpz_class(0), m_efac);
      for (unsigned int col = 0; col < basis.size2(); col++) {
        int numTerms = 0;
        Expr poly = nullptr;
        double coef = 1;
        double intpart;

        while (coef < 1000 /* upper bound on coef/const */) {
          for (unsigned int row = 0; row < basis.size1(); row++) {
            double cur = basis(row,col) * coef;
            Expr mult;
            Expr monomialExpr = monomialToExpr[row];

            auto tmp = std::modf(cur, &intpart);
            if (- approxEqualTol >= tmp || tmp >= approxEqualTol) {
              double c = 1/(cur-intpart);
              tmp = std::modf(c, &intpart);
              if (- approxEqualTol < tmp && tmp < approxEqualTol) {
                coef *= c;
              } else {
                coef *= 10;
              }
              poly = nullptr;
              break;
            }
            else
  /*        if (abstractVar != nullptr && (isNumericConst(monomialExpr) || curPolyDegree > 1)) {
              if (!isNumericConst(monomialExpr)) {
                mult = mk<MULT>(abstractVar, monomialExpr);
              } else {
                int monomialInt = lexical_cast<int>(monomialExpr);
                //assumption is that abstractVar will be of the form intConst * var or var * intConst
                bool success = true;
                Expr var = nullptr;
                cpp_int varCoeff = 1;
                if (!isOpX<MULT>(abstractVar)) {
                  success = false;
                } else {
                  for (auto it = abstractVar->args_begin(), end = abstractVar->args_end(); it != end; ++it) {
                    if (isNumericConst(*it)) {
                      varCoeff = lexical_cast<cpp_int>(*it);
                    } else if (bind::isIntConst(*it)) {
                      var = *it;
                    } else {
                      success = false;
                    }
                  }
                }
                if (!success || var == nullptr) {
                  mult = mk<MULT>(abstractVar, monomialExpr);
                } else {
                  mult = mk<MULT>(mkMPZ(varCoeff*monomialInt, m_efac), var);
                }
              }
            } else */
            {
              mult = mk<MULT>(mkMPZ(cpp_int(cur), m_efac), monomialToExpr[row]);
            }

            if (poly != nullptr) {
              poly = mk<PLUS>(poly, mult);
            } else {
              poly = mult;
            }
            numTerms++;
          }
          if (poly == nullptr) continue;
          if (poly != nullptr && numTerms > 1) {
            poly = mk<EQ>(poly, zero);
            polynomials.push_back(poly);
            break;
          }
        }
      }

      return 0;
    }

    void
    addpolytocands(ExprSet & cands, Expr poly)
    {
      cands.insert(poly);
    }

    void
    addpolytocands(ExprVector & cands, Expr poly)
    {
      cands.push_back(poly);
    }

    int
    initInvVars(Expr invDecl, ExprVector& vars, map<unsigned int, Expr>& monomialToExpr)
    {
      int numVars = 0;
      monomialToExpr.insert(pair<unsigned int, Expr>(0, mkTerm(mpz_class(1), m_efac)));

      for (Expr i : vars) {
        numVars++;
        monomialToExpr.insert(pair<unsigned int, Expr>(numVars, i));
      }

      //degree 2 monomials
      for (unsigned int vIndex1 = 1, mIndex = numVars+1; vIndex1 <= numVars; vIndex1++) {
        for (int vIndex2 = vIndex1; vIndex2 <= numVars; vIndex2++) {
          monomialToExpr.insert(std::pair<unsigned int, Expr>(mIndex,
                        mk<MULT>(monomialToExpr[vIndex1],
                           monomialToExpr[vIndex2])));
          mIndex++;
        }
      }

      return numVars;
    }

    // adds monomial and constant multiples of it if corresponding
    // monomial column in datamatrix is constant
    void
    initLargeCoeffToExpr(const Matrix &dataMatrix)
    {
      // first column is 1's
      for (unsigned int col = 1; col < dataMatrix.size2(); col++) {

        double tmp = dataMatrix(0, col);
        unsigned int row;

        for (row = 1; row < dataMatrix.size1(); row++) {
          if (!approxEqual(dataMatrix(row, col), tmp)) {
              break;
            }
        }

//        if (row != dataMatrix.n_rows) {
//          continue;
//        }
//
//        Expr var = monomialToExpr[col];
//        for (int multiple = 1; multiple < 4; multiple++) {
//          Expr val1 = mk<MULT>(mkTerm(mpz_class(multiple), m_efac), var);
//          Expr val2 = mk<MULT>(mkTerm(mpz_class(-1*multiple), m_efac), var);
//          largeCoeffToExpr.insert(make_pair(multiple*tmp, val1));
//          largeCoeffToExpr.insert(make_pair(-1*multiple*tmp, val2));
//        }

      }
    }

    // return true only if all the data satisfies basis
    bool
    checkBasisSatisfiesData(const Matrix &monomial, const Vector &basis)
    {
      if (monomial.size2() != basis.size()) {
        return false;
      }

      for (unsigned int row = 0; row < monomial.size1(); row++) {
        double sum = 0;
        for (unsigned int col = 0; col < monomial.size2(); col++) {
          sum += basis(col) * monomial(row, col);
        }
        if (!approxEqual(sum, 0)) {
          return false;
        }
      }

      return true;

    }

    template <class CONTAINERT>
    int
    getPolynomialsFromData(const Matrix & data, CONTAINERT & cands, Expr inv, map<unsigned int, Expr>& monomialToExpr, Expr assume = nullptr)
    {
      ExprSet polynomialsComputed;
      vector<Matrix> basisComputed;
      basisComputed.push_back(Matrix());
      basisComputed.push_back(Matrix());
      basisComputed.push_back(Matrix());

      if (data.size1() == 0 || data.size2() == 0) {
        return -1;
      }

      clock_t start = clock();

      Matrix monomialMatrix = computeMonomial(data);

      Matrix basis = gaussjordan(monomialMatrix);

      //      printmsg(INFO, "before basis check ", basis);

      if (basis.size2() == 0) {
        return 0;
      }

      //      cout << endl << basis << endl; //DEBUG

      // computetime("basis computation time ", start);

      // check if column of basis is unique
      if (assume == nullptr) {
        for (unsigned int col = 0; col < basis.size2(); col++) {
          unsigned int oldcol;
          for (oldcol = 0; oldcol < basisComputed[curPolyDegree].size2(); oldcol++) {
            if (columnsApproxEqual(basis, col, basisComputed[curPolyDegree], oldcol)) {
              shedColumn(basis, col);
              break;
            }
          }
        }

        for (unsigned int col = 0; col < basis.size2(); col++) {
          appendColumn(basisComputed[curPolyDegree], getColumn(basis, col));
        }
      }

      // computetime("data unique check time ", start);

      // for some reason previous monomialmatrix is overwritten so copy to a different matrix
      Matrix monomialMatrix2 = computeMonomial(data);
      for (unsigned int col = 0; col < basis.size2(); col++) {
        if (!checkBasisSatisfiesData(monomialMatrix2, getColumn(basis, col))) {
          shedColumn(basis, col);
          continue;
        }

      }

      // if (assume != nullptr) {
      // 	printmsg(INFO, "\n dataMatrix \n", dataMatrix);
      // 	printmsg(INFO, "\n data \n", data);
      // 	printmsg(INFO, "\n monomial \n", monomialMatrix);
      // 	printmsg(INFO, "\n basis \n", basis);
      // }

      vector<Expr> polynomials;
      polynomials.reserve(basis.size2());

      if (!algExprFromBasis(basis, polynomials, monomialToExpr)) {
        for (auto poly : polynomials) {
          Expr cand = (assume == nullptr) ? poly : mk<IMPL>(assume, poly);
          if (polynomialsComputed.find(cand) == polynomialsComputed.end()) {
            addpolytocands(cands, cand);
            polynomialsComputed.insert(cand);
            printmsg(DEBUG, "Adding polynomial: ", cand);
          }
        }

        computetime("poly conversion time ", start);

        return polynomials.size();
      }

      return 0;

    }

  public:

    DataLearner(CHCs& r, EZ3 &z3, int to, bool debug) :
      ruleManager(r), bnd(ruleManager, to, debug), m_efac(r.m_efac), curPolyDegree(1) {}

    void
    setLogLevel(unsigned int l)
    {
      LOG_LEVEL = l;
    }

    map <Expr, vector< vector<double> > > exprToModels;
    map <Expr, ExprVector> invVars;

    bool computeData(map<Expr, ExprVector>& arrRanges, map<Expr, ExprSet>& constr)
    {
      exprToModels.clear();
      invVars.clear();
      return bnd.unrollAndExecuteMultiple(invVars, exprToModels, arrRanges, constr);
    }

    void computeDataSplit(Expr srcRel, Expr splitter, Expr invs, bool fwd, ExprSet& constr)
    {
      exprToModels.clear();
      invVars.clear();
      bnd.unrollAndExecuteSplitter(srcRel, invVars[srcRel], exprToModels[srcRel], splitter, invs, fwd, constr);
    }

    ExprSet& getConcrInvs(Expr rel) { return bnd.concrInvs[rel]; }

    // Implementation of "A Data Driven Approach for Algebraic Loop Invariants", Sharma et al.
    // return number of candidate polynomials added (< 0 in case of error)
    template <class CONTAINERT> void
    computePolynomials(Expr inv, CONTAINERT & cands)
    {
      CONTAINERT tmp;
      while (!exprToModels[inv].empty())
      {
        const auto &models = exprToModels[inv];
        const unsigned int rows = models.size();
        const unsigned int cols = models.front().size() + 1;
        Matrix dataMatrix(rows, cols);
        for (unsigned int r = 0; r < rows; r++) {
          dataMatrix(r, 0) = 1;
          for (unsigned int c = 1; c < cols; c++)
            dataMatrix(r, c) = models[r][c - 1];
        }

        map<unsigned int, Expr> monomialToExpr;
        if (0 == initInvVars(inv, invVars[inv], monomialToExpr)) return;
        initLargeCoeffToExpr(dataMatrix);
        getPolynomialsFromData(dataMatrix, tmp, inv, monomialToExpr);
        if (tmp.size() > 0) break;
        else exprToModels[inv].pop_back();
      }
      cands.insert(tmp.begin(), tmp.end());
    }
  };
}


#endif
