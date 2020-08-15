#pragma once

#include <fstream>
#include <string>
#include <vector>
#include <boost/dynamic_bitset.hpp>

class aigman {
public:
  int nPis;
  int nPos;
  int nLats;
  int nGates;
  int nObjs;
  std::vector<int> vPos;
  std::vector<int> vLos;
  std::vector<int> vLis;
  std::vector<int> vObjs;
  
  std::vector<int> vValues;
  
  std::vector<bool> vDeads;
  std::vector<std::vector<int> > vvFanouts;
  std::vector<int> vLevels;

  std::vector<aigman> backup;
  
  aigman() {};
  aigman(int nPis, int nLats = 0) : nPis(nPis), nLats(nLats) {
    nObjs = nPis + nLats + 1;
  };

  aigman &operator=(const aigman & x) {
    nPis == x.nPis;
    nPos = x.nPos;
    nLats == x.nLats;
    nGates = x.nGates;
    nObjs = x.nObjs;
    vPos = x.vPos;
    vLos = x.vLos;
    vLis = x.vLis;
    vObjs = x.vObjs;
    vValues = x.vValues;
    vDeads = x.vDeads;
    vvFanouts = x.vvFanouts;
    vLevels = x.vLevels;
    return *this;
  }

  void negate() {
    for(int i = 0; i < nPos; i++) {
      vPos[i] = vPos[i] ^ 1;
    }
  }

  void read(std::string filename);
  void write(std::string filename);
  
  int renumber_rec(int i, std::vector<int> & vObjsNew, int & nObjsNew);
  void renumber();
  
  int getvalue(int i);
  void simulate(std::vector<int> const & inputs);
  void simulate(std::vector<boost::dynamic_bitset<> > const & inputs, std::vector<boost::dynamic_bitset<> > & outputs);
  double eval(std::vector<boost::dynamic_bitset<> > const & inputs, std::vector<boost::dynamic_bitset<> > const & outputs);
  double eval(std::vector<boost::dynamic_bitset<> > const & inputs, boost::dynamic_bitset<> const & output) { std::vector<boost::dynamic_bitset<> > outputs = {output}; return eval(inputs, outputs); }

  void supportfanouts_rec(int i);
  void supportfanouts();
  void removenode(int i);
  void replacenode(int i, int j, bool prop = 1);

  int supportlevels();

  void markfocone_rec(int i);

  void save(int i = 0);
  void load(int i = 0);

  int newobj(int i, int j);
  void newpo(int i);

  int newor(int i, int j);
  int newite(int c, int t, int e);
};
