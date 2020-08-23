#include <iostream>
#include <cstring>

#include "pla.h"
#include "bddlearn.h"

int main(int argc, char** argv) {
  if(argc < 3) {
    std::cerr << "usage : lnet [-r] <pla> <pla2> ... <output>" << std::endl;
    return 1;
  }

  std::string outname = argv[argc - 1];
  bool reo = 0;
  
  // read pla files
  std::vector<boost::dynamic_bitset<> > inputs;
  std::vector<boost::dynamic_bitset<> > outputs;
  for(int i = 1; i < argc - 1; i++) {
    if(strcmp(argv[i], "-r") == 0) {
	reo = 1;
	continue;
      }
    pla2pat(argv[i], inputs, outputs);
  }

  // separate evaluation sets
  double ratio = 0.5;
  std::vector<boost::dynamic_bitset<> > traininputs;
  std::vector<boost::dynamic_bitset<> > trainoutputs;
  std::vector<boost::dynamic_bitset<> > evalinputs(inputs.size());
  std::vector<boost::dynamic_bitset<> > evaloutputs(outputs.size());
  {
    int total = inputs[0].size();
    int train = total * ratio;
    traininputs = inputs;
    for(int j = 0; j < inputs.size(); j++) {
      traininputs[j].resize(train);
      for(int i = train; i < total; i++) {
	evalinputs[j].push_back(inputs[j][i]);
      }
    }
    trainoutputs = outputs;
    for(int j = 0; j < outputs.size(); j++) {
      trainoutputs[j].resize(train);
      for(int i = train; i < total; i++) {
	evaloutputs[j].push_back(outputs[j][i]);
      }
    }
  }

  bddlearn(traininputs, trainoutputs[0], outname, reo, evalinputs, evaloutputs[0]);

  aigman aig;
  aig.read(outname);
  std::cout << "tran " << aig.eval(traininputs, trainoutputs) << std::endl;
  std::cout << "eval " << aig.eval(evalinputs, evaloutputs) << std::endl;
  
  return 0;
}
