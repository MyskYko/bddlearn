#include <iostream>
#include <random>
#include <cstring>

#include "aig.hpp"
#include "pla.h"

int main(int argc, char** argv) {
  if(argc < 4) {
    std::cerr << "usage : exe <aig> <npats> <out.pla> [-ef]" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  int npats = atoi(argv[2]);
  std::string planame = argv[3];
  int fex = 0;
  if(argc > 4 && strcmp(argv[4], "-e") == 0) fex = 1;
  if(argc > 4 && strcmp(argv[4], "-f") == 0) fex = 2;
  
  // read aig
  aigman aig;
  aig.read(aigname);

  // generate patterns
  std::vector<boost::dynamic_bitset<> > inputs(aig.nPis);
  std::random_device rd;
  std::mt19937 mt(rd());
  for(int i = 0; i < inputs.size(); i++) {
    inputs[i].resize(npats);
    for(int j = 0; j < npats; j++) {
      inputs[i][j] = mt() % 2;
    }
  }

  if(fex) {
    boost::dynamic_bitset<> pat;
    pat.resize(inputs.size());
    std::random_device rd;
    std::mt19937 mt(rd());
    for(int i = 0; i < inputs.size(); i++)
      pat[i] = mt() % 2;
    int count = 1;
    for(int i = 0; i < inputs.size(); i++)
      inputs[i][npats - count] = pat[i];
    count++;
    if(fex == 1) {
      for(int j = 0; j < inputs.size(); j++) {
	for(int i = 0; i < inputs.size(); i++) {
	  if(i == j) inputs[i][npats - count] = !pat[i];
	  else inputs[i][npats - count] = pat[i];
	}
	count++;
	if(npats < count) {
	  std::cout << "bit flip patterns exceed " << npats << std::endl;
	  abort();
	}
      }
    }
    else if(fex == 2) {
      for(int j = 0; j < inputs.size(); j++) {
	for(int k = j + 1; k < inputs.size() + 1; k++) {
	  for(int i = 0; i < inputs.size(); i++) {
	    if(i == j || i == k) inputs[i][npats - count] = !pat[i];
	    else inputs[i][npats - count] = pat[i];
	  }
	  count++;
	  if(npats < count) {
	    std::cout << "two-bit flip patterns exceed " << npats << std::endl;
	    abort();
	  }
	}
      }
    }
  }

  // simulate
  std::vector<boost::dynamic_bitset<> > outputs;
  aig.simulate(inputs, outputs);

  // write pla
  pat2pla(planame, inputs, outputs);
  
  return 0;
}
