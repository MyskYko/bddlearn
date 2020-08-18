#include <iostream>

#include "pla.h"
#include "bddlearn.h"

int main(int argc, char** argv) {
  if(argc < 3) {
    std::cerr << "usage : lnet <pla> <pla2> ... <output>" << std::endl;
    return 1;
  }

  std::string outname = argv[argc - 1];

  // read pla files
  std::vector<boost::dynamic_bitset<> > inputs;
  std::vector<boost::dynamic_bitset<> > outputs;
  for(int i = 1; i < argc - 1; i++) {
    pla2pat(argv[i], inputs, outputs);
  }

  // separate evaluation sets
  double ratio = 1;
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

  bddlearn(traininputs, trainoutputs[0], outname, 0);
  bddlearn(traininputs, trainoutputs[0], outname, 1);
  
  return 0;
}
