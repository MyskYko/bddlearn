#include <iostream>

#include "aig.hpp"

int main(int argc, char** argv) {
  if(argc < 3) {
    std::cerr << "usage : exe <aig> <out.aig>" << std::endl;
    return 1;
  }
  std::string aigname = argv[1];
  std::string aigname2 = argv[2];

  // read aig
  aigman aig;
  aig.read(aigname);

  // order pi
  std::vector<int> order;
  for(int i = 0; i < aig.nPis; i++) {
    order.push_back(i);
  }
  for(int i = 0; i < aig.nPis / 2; i++) {
    {
      int pos = std::distance(order.begin(), std::find(order.begin(), order.end(), aig.nPis / 2 - i - 1));
      if(i + i != pos) {
	aig.swappis(i + i, pos);
	std::swap(order[i + i], order[pos]);
      }
    }
    {
      int pos = std::distance(order.begin(), std::find(order.begin(), order.end(), aig.nPis - i - 1));
      if(i + i + 1 != pos) {
	aig.swappis(i + i + 1, pos);
	std::swap(order[i + i + 1], order[pos]);
      }
    }
  }


  aig.write(aigname2);
  
  return 0;
}
