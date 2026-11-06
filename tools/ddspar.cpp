// ddspar: print DDS's par score for a deal, from North-South's point of view.
//
// The score goes to stdout, and the par contracts DDS lists go to stderr for information.
// Nothing here is trusted: `ddscheck --par` compares the score with the proved value.
//
// Usage: ddspar --pbn "N:..." --vul none|both|ns|ew --dealer N|E|S|W
#include <api/dll.h>

#include <cstdio>
#include <string>

int main(int argc, char** argv) {
  std::string pbn, vul_name, dealer_name;
  for (int i = 1; i + 1 < argc; i += 2) {
    std::string flag = argv[i];
    if (flag == "--pbn") pbn = argv[i + 1];
    else if (flag == "--vul") vul_name = argv[i + 1];
    else if (flag == "--dealer") dealer_name = argv[i + 1];
  }
  const std::string vuls[4] = {"none", "both", "ns", "ew"};
  int vul = -1;
  for (int v = 0; v < 4; v++)
    if (vul_name == vuls[v]) vul = v;
  size_t dealer = dealer_name.size() == 1 ? std::string("NESW").find(dealer_name[0]) : std::string::npos;
  if (pbn.size() >= sizeof(DdTableDealPBN{}.cards) || vul < 0 || dealer == std::string::npos) {
    fprintf(stderr, "usage: ddspar --pbn \"N:...\" --vul none|both|ns|ew --dealer N|E|S|W\n");
    return 2;
  }

  SetMaxThreads(1);
  DdTableDealPBN deal{};
  pbn.copy(deal.cards, pbn.size());
  DdTableResults table{};
  ParResultsDealer par{};
  int rc = CalcDDtablePBN(deal, &table);
  if (rc == RETURN_NO_FAULT) rc = DealerPar(&table, &par, static_cast<int>(dealer), vul);
  if (rc != RETURN_NO_FAULT) {
    char message[80];
    ErrorMessage(rc, message);
    fprintf(stderr, "DDS error: %s\n", message);
    return 2;
  }
  fprintf(stderr, "DDS par contracts:");
  for (int i = 0; i < par.number; i++) fprintf(stderr, " %s", par.contracts[i]);
  fprintf(stderr, "\n");
  printf("%d\n", par.score);
}
