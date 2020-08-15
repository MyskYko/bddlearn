#include <iostream>
#include <random>

#include "aig.hpp"
#include "pla.h"

int main(int argc, char** argv) {
  if(argc < 4) {
    std::cerr << "usage : exe <aig> <npats> <out.pla>" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  int npats = atoi(argv[2]);
  std::string planame = argv[3];

  // read aig
  aigman aig;
  aig.read(aigname);

  // generate patterns
  std::vector<boost::dynamic_bitset<> > inputs(aig.nPis);
  std::mt19937 mt;
  for(int i = 0; i < inputs.size(); i++) {
    inputs[i].resize(npats);
    for(int j = 0; j < npats; j++) {
      inputs[i][j] = mt() % 2;
    }
  }

  // simulate
  std::vector<boost::dynamic_bitset<> > outputs;
  aig.simulate(inputs, outputs);

  // write pla
  pat2pla(planame, inputs, outputs);
  
  return 0;
}
