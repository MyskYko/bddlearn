#include <iostream>

#include "aig.hpp"

int main(int argc, char** argv) {
  if(argc < 3) {
    std::cerr << "usage : exe <aig> <out.aig> [nargs]" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  std::string aigname2 = argv[2];
  int nargs = 2;
  if(argc > 3) nargs = atoi(argv[3]);

  // read aig
  aigman aig;
  aig.read(aigname);

  // order pi
  std::vector<int> order;
  for(int i = 0; i < aig.nPis; i++) {
    order.push_back(i);
  }
  for(int i = 0; i < aig.nPis / nargs; i++) {
    for(int j = 0; j < nargs; j++) {
      int pos = std::distance(order.begin(), std::find(order.begin(), order.end(), aig.nPis * (j + 1) / nargs - i - 1));
      if(i + i + j != pos) {
	aig.swappis(i + i + j, pos);
	std::swap(order[i + i + j], order[pos]);
      }
    }
  }


  aig.write(aigname2);
  
  return 0;
}
