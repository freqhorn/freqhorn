#include "deep/BndExpl.hpp"

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

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1){
    outs () <<
        "* * *            Bounded Explorer (FreqHorn's supplementary tool) v.0.6 - Copyright (C) 2021           * * *\n" <<
        "                                           Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " expl [--help]               show help\n" <<
        " expl [options] <file.smt2>  find counterexamples for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        " --upto                      max unrollong depth (default: 10000)\n" <<
        " --skip-elim                 do not minimize CHC rules (and do not slice)\n"
        " --to                        timeout for each Z3 run in ms (default: 1000)\n" <<
        " --debug                     print debugging information during run\n\n";

    return 0;
  }

  unrollAndCheck(string(argv[argc-1]), 1,
                 getIntValue("--upto", 10000, argc, argv),
                 getIntValue("--to", 1000, argc, argv),
                 getBoolValue("--skip-elim", false, argc, argv),
                 getIntValue("--debug", false, argc, argv));

  return 0;
}
