#include "deep/RndLearnerV2.hpp"
#include "deep/RndLearnerV3.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      char* p;
      int num = strtol(argv[i+1], &p, 10);
      if (*p) return 1;      // if used w/o arg, return boolean
      else return num;
    }
  }
  return defValue;
}

void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      values.push_back(string(argv[i+1]));
    }
  }
}

int main (int argc, char ** argv)
{
  const char *OPT_HELP = "--help";
  const char *OPT_V1 = "--v1";
  const char *OPT_V2 = "--v2";
  const char *OPT_V3 = "--v3";
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_TO = "--to";
  const char *OPT_K_IND = "--kind";
  const char *OPT_ITP = "--itp";
  const char *OPT_BATCH = "--batch";
  const char *OPT_RETRY = "--retry";
  const char *OPT_ELIM = "--skip-elim";
  const char *OPT_ARITHM = "--skip-arithm";
  const char *OPT_SEED = "--skip-syntax";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";
  const char *OPT_DATA_LEARNING = "--data";
  const char *OPT_MUT = "--mut";
  const char *OPT_PROP = "--prop";
  const char *OPT_DISJ = "--disj";
  const char *OPT_D1 = "--all-mbp";
  const char *OPT_D2 = "--phase-prop";
  const char *OPT_D3 = "--phase-data";
  const char *OPT_D4 = "--stren-mbp";
  const char *OPT_D5 = "--fwd";
  const char *OPT_D6 = "--prune";
  const char *OPT_REC = "--re";
  const char *OPT_MBP = "--eqs-mbp";
  const char *OPT_SER = "--serialize";
  const char *OPT_DEBUG = "--debug";

  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                                 FreqHorn v.0.6 - Copyright (C) 2021                                 * * *\n" <<
        "                                           Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqhorn [--help]               show help\n" <<
        " freqhorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        " " << OPT_V1 << "                            original version (one-by-one sampling)\n"
        " " << OPT_V2 << "                            optimized version for transition systems (+ bootstrapping)\n"
        " " << OPT_V3 << " (default)                  optimized version (+ bootstrapping, propagation, and data candidates)\n"
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        "                                 (if not specified, sample from uniform distributions)\n" <<
        " " << OPT_MAX_ATTEMPTS << " <N>                  maximal number of candidates to sample and check\n" <<
        " " << OPT_ELIM << "                     do not minimize CHC rules (and do not slice)\n" <<
        " " << OPT_ARITHM << "                   do not apply arithmetic constant propagation during parsing\n" <<
        " " << OPT_TO << "                            timeout for each Z3 run in ms (default: 1000)\n" <<
        " " << OPT_SER << "                     serialize the intermediate CHC representation to `chc.smt2` (and exit)\n" <<
        " " << OPT_DEBUG << " <LVL>                   print debugging information during run (default level: 0)\n\n" <<
        "V1 options only:\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_K_IND << "                          run k-induction after each learned lemma\n\n" <<
        "V2 options only:\n" <<
        " " << OPT_ITP << "                           bound for itp-based proofs\n" <<
        " " << OPT_BATCH << "                         threshold for how many candidates to check at once\n" <<
        " " << OPT_RETRY << "                         threshold for how many lemmas to wait before giving failures a second chance\n\n" <<
        "V3 options only:\n" <<
        " " << OPT_DATA_LEARNING << " <N>                      bootstrap candidates from behaviors (0: no, NUM: rounds)\n" <<
        "                                 (if \"" << OPT_DISJ <<"\" is enabled, then default is 1; otherwise, 0)\n\n" <<
        " " << OPT_MUT << "                           level of mutation for bootstrapped candidates (0: no, 1: (default), 2: full)\n" <<
        " " << OPT_SEED << "                   do not analyze syntax for seeds mining, except of the query\n" <<
        "                                 (thus, will disable quantified invariants)\n" <<
        " " << OPT_MBP << "                       break equalities while MBP generation (0: no (default), 1: yes, 2: both)\n" <<
        " " << OPT_REC << "                            weaken and recycle data candidates\n" <<
        " " << OPT_PROP << " <N>                      rounds of candidate propagation before bootstrapping\n" <<
        "                                 (if \"" << OPT_DISJ <<"\" is enabled, then default is 1; otherwise, 0)\n\n" <<
        "ImplCheck options only (\"" << OPT_DATA_LEARNING << "\" will be enabled automatically):\n" <<
        " " << OPT_DISJ << "                          generate disjunctive invariants\n" <<
        " " << OPT_D1 << "                       search for phases among all MBPs\n" <<
        " " << OPT_D2 << "                    propagate phase lemmas across guards\n" <<
        " " << OPT_D3 << "                    datalearn phase lemmas\n" <<
        " " << OPT_D4 << "                     strengthen MBP with abduction\n" <<
        " " << OPT_D5 << "                           direction of phase discovery (0: backward, 1: forward (default), 2: both)\n" <<
        " " << OPT_D6 << "                         do not consider duplicates of data candidates (needs \"" << OPT_DATA_LEARNING <<"\")\n";

    return 0;
  }

  bool vers1 = getBoolValue(OPT_V1, false, argc, argv);
  bool vers2 = getBoolValue(OPT_V2, false, argc, argv);
  bool vers3 = getBoolValue(OPT_V3, false, argc, argv);
  if (vers1 + vers2 + vers3 > 1)
  {
    outs() << "Only one version of the algorithm can be chosen.\n";
    return 0;
  }

  if (!vers1 && !vers2 && !vers3) vers3 = true; // default

  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  int itp = getIntValue(OPT_ITP, 0, argc, argv);
  int batch = getIntValue(OPT_BATCH, 3, argc, argv);
  int retry = getIntValue(OPT_RETRY, 3, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  bool d_se = !getBoolValue(OPT_SEED, false, argc, argv);
  int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  int do_dl = getIntValue(OPT_DATA_LEARNING, 0, argc, argv);
  int do_mu = getIntValue(OPT_MUT, 1, argc, argv);
  int mbp_eqs = getIntValue(OPT_MBP, 1, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  int d_f = getIntValue(OPT_D5, 1, argc, argv);
  bool d_g = !getBoolValue(OPT_D6, false, argc, argv);
  bool d_r = getBoolValue(OPT_REC, false, argc, argv);
  bool d_ser = getBoolValue(OPT_SER, false, argc, argv);
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);

  if (d_m || d_p || d_d || d_s) do_disj = true;
  if (do_disj)
  {
    if (!d_p && !d_d)
    {
      if (debug) errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled. "
                        << "Enabling \"" << OPT_D3 << "\".\n";
      d_d = true;
    }
    if (!d_se)
    {
      if (debug) errs() << "WARNING: \"" << OPT_SEED << "\" and \"" << OPT_DISJ << "\" are incompatible. "
                        << "Ignoring \"" << OPT_SEED << "\".\n";
      d_se = true;
    }
    if (do_prop == 0) do_prop = 1;
    if (do_dl == 0) do_dl = 1;
  }

  if (vers3)      // FMCAD'18 + CAV'19 + new experiments
    learnInvariants3(string(argv[argc-1]), max_attempts, to, densecode, aggressivepruning,
                     do_dl, do_mu, do_elim, do_arithm, do_disj, do_prop, mbp_eqs,
                     d_m, d_p, d_d, d_s, d_f, d_r, d_g, d_se, d_ser, debug);
  else if (vers2) // run the TACAS'18 algorithm
    learnInvariants2(string(argv[argc-1]), to, max_attempts,
                  itp, batch, retry, densecode, aggressivepruning, debug);
  else            // run the FMCAD'17 algorithm
    learnInvariants(string(argv[argc-1]), to, max_attempts,
                  kinduction, itp, densecode, addepsilon, aggressivepruning, debug);
  return 0;
}
