#include <iostream>
#include <fstream>
#include <sstream>
#include <algorithm>
#include <cassert>

#include "pla.h"

using namespace std;

void pla2pat(string filename, vector<boost::dynamic_bitset<> > & inputs, vector<boost::dynamic_bitset<> > & outputs) {
  ifstream f(filename);
  int ninputs = -1;
  int noutputs = -1;
  int npats_new = -1;
  string str;
  while(getline(f, str)) {
    if(str.empty()) continue;
    if(str[0] == '.') {
      if(str[1] == 'i') {
	ninputs = stoi(str.substr(3));
      }
      else if(str[1] == 'o') {
	noutputs = stoi(str.substr(3));
      }
      else if(str[1] == 'p') {
	npats_new = stoi(str.substr(3));
      }
      continue;
    }
    break;
  }

  if(ninputs < 0 || noutputs < 0) {
    stringstream ss(str);
    string s;
    getline(ss, s, ' ');
    assert(ninputs < 0 || ninputs == s.size());
    ninputs = str.size();
    getline(ss, s, ' ');
    assert(noutputs < 0 || noutputs == s.size());
    noutputs = s.size();
  }

  if(inputs.empty()) {
    inputs.resize(ninputs);
  }
  if(outputs.empty()) {
    outputs.resize(noutputs);
  }
  assert(inputs.size() == ninputs);
  assert(outputs.size() == noutputs);

  int npats = inputs[0].size();
  for(int i = 0; i < ninputs; i++) {
    assert(inputs[i].size() == npats);
    if(npats_new > 0) {
      inputs[i].reserve(npats + npats_new);
    }
  }
  for(int i = 0; i < noutputs; i++) {
    assert(outputs[i].size() == npats);
    if(npats_new > 0) {
      outputs[i].reserve(npats + npats_new);
    }
  }
  
  do {
    if(str.empty()) continue;
    if(str[0] == '.') break;
    int i;
    for(i = 0; i < ninputs; i++) {
      assert(str[i] == '1' || str[i] == '0');
      if(str[i] == '1') {
	inputs[i].push_back(1);
      }
      else {
	inputs[i].push_back(0);
      }
    }
    while(str[i] == ' ') i++;
    for(int j = 0; j < noutputs; j++) {
      if(str[i + j] == '1') {
	outputs[j].push_back(1);
      }
      else {
	outputs[j].push_back(0);
      }
    }
    npats++;
  } while(getline(f, str));
}

void pat2pla(string filename, vector<boost::dynamic_bitset<> > const & inputs, vector<boost::dynamic_bitset<> > const & outputs) {
  for(int i = 1; i < inputs.size(); i++) {
    assert(inputs[i].size() == inputs[0].size());
  }
  for(int i = 0; i < outputs.size(); i++) {
    assert(outputs[i].size() == inputs[0].size());
  }
  ofstream f(filename);
  f << ".i " << inputs.size() << endl;
  f << ".o " << outputs.size() << endl;
  f << ".p " << inputs[0].size() << endl;
  f << ".type fr" << endl;
  for(int i = 0; i < inputs[0].size(); i++) {
    for(int j = 0; j < inputs.size(); j++) {
      f << inputs[j][i];
    }
    f << " ";
    for(int j = 0; j < outputs.size(); j++) {
      f << outputs[j][i];
    }
    f << endl;
  }
  f << ".e" << endl;
}

void patunique(vector<boost::dynamic_bitset<> > & inputs, vector<boost::dynamic_bitset<> > & outputs) {
  int ninputs = inputs.size();
  int noutputs = outputs.size();
  assert(noutputs == 1);
  int npats = inputs[0].size();
  int nObjs = 1;
  int nObjsAlloc = ninputs * npats;
  int * pObjs = (int *)calloc(nObjsAlloc * 2, sizeof(int));
  assert(pObjs);
  int root = 0;

  std::vector<int> remove_indices;
  
  for(int j = 0; j < npats; j++) {
    int * p = &root;
    for(int i = 0; i < ninputs; i++) {
      if(inputs[i][j]) {
	p = pObjs + *p + *p + 1;
      }
      else {
	p = pObjs + *p + *p;
      }
      if(i < ninputs - 1 && !(*p)) {
	*p = nObjs++;
      }
    }
    if(*p) {
      if(*p > 0 && !outputs[0][j]) {
	remove_indices.push_back(*p - 1);
      }
      if(*p < 0 && outputs[0][j]) {
	remove_indices.push_back(- *p - 1);
      }
      remove_indices.push_back(j);
    }
    else {
      *p = outputs[0][j]? j + 1: - j - 1;
    }
  }

  free(pObjs);

  std::sort(remove_indices.begin(), remove_indices.end());
  remove_indices.erase(std::unique(remove_indices.begin(), remove_indices.end()), remove_indices.end());

  for(int k = remove_indices.size() - 1; k >= 0; k--) {
    int j = remove_indices[k];
    if(j == npats - 1) {
      npats--;
      continue;
    }
    //    std::cout << "remove ";
    for(int i = 0; i < ninputs; i++) {
      //      std::cout << inputs[i][j];
      inputs[i][j] = inputs[i][npats - 1];
    }
    //    std::cout << " " << outputs[0][j] << std::endl;
    outputs[0][j] = outputs[0][npats - 1];
    npats--;
  }
  for(int i = 0; i < ninputs; i++) {
    inputs[i].resize(npats);
  }
  outputs[0].resize(npats);
}

double plaeval(string filename, vector<boost::dynamic_bitset<> > const & inputs, vector<boost::dynamic_bitset<> > const & outputs) {
  ifstream f(filename);
  int ninputs = -1;
  int noutputs = -1;
  int npats = -1;
  string str;
  while(getline(f, str)) {
    if(str.empty()) continue;
    if(str[0] == '.') {
      if(str[1] == 'i') {
	ninputs = stoi(str.substr(3));
      }
      else if(str[1] == 'o') {
	noutputs = stoi(str.substr(3));
      }
      else if(str[1] == 'p') {
	npats = stoi(str.substr(3));
      }
      continue;
    }
    break;
  }
  
  if(ninputs < 0 || noutputs < 0) {
    stringstream ss(str);
    string s;
    getline(ss, s, ' ');
    assert(ninputs < 0 || ninputs == s.size());
    ninputs = str.size();
    getline(ss, s, ' ');
    assert(noutputs < 0 || noutputs == s.size());
    noutputs = s.size();
  }

  assert(inputs.size() == ninputs);
  assert(outputs.size() == noutputs);
  
  if(npats < 0) {
    npats = 5000;
  }
  
  int nObjs = 1;
  int nObjsAlloc = ninputs * npats;
  int * pObjs = (int *)calloc(nObjsAlloc * 3, sizeof(int));
  assert(pObjs);
  int root = 0;
  
  do {
    if(str.empty()) continue;
    if(str[0] == '.') break;
    int i = 0;
    int * p = &root;
    while(1) {
      assert(str[i] == '1' || str[i] == '0' || str[i] == '-');
      if(str[i] == '0') {
	p = pObjs + *p + *p + *p;
      }
      else if(str[i] == '1') {
	p = pObjs + *p + *p + *p + 1;
      }
      else {
	p = pObjs + *p + *p + *p + 2;
      }
      i++;
      if(i == ninputs) {
	break;
      }
      if(!(*p)) {
	*p = nObjs++;
	if(nObjsAlloc == nObjs) {
	  int pos = p - pObjs;
	  pObjs = (int *)realloc(pObjs, (nObjsAlloc + nObjsAlloc) * 3 * sizeof(int));
	  assert(pObjs);
	  for(int j = 0; j < nObjsAlloc * 3; j++) {
	    pObjs[j + nObjsAlloc * 3] = 0;
	  }
	  nObjsAlloc = nObjsAlloc + nObjsAlloc;
	  p = pObjs + pos;
	}
      }
    }
    while(str[i] == ' ') i++;
    assert(noutputs < 32);
    int value = 0;
    for(int j = 0; j < noutputs; j++) {
      if(str[i + j] == '1') {
	value += 1 << j;
      }
    }
    assert(value); // assume onset
    assert(!(*p) || *p == value);
    *p = value;
  } while(getline(f, str));

  int count = 0;
  vector<int *> * ps = new vector<int *>;
  vector<int *> * psnext = new vector<int *>;
  for(int i = 0; i < inputs[0].size(); i++) {
    ps->clear();
    ps->push_back(&root);
    for(int j = 0; j < ninputs; j++) {
      psnext->clear();
      if(!inputs[j][i]) {
	for(int * p : *ps) {
	  p = pObjs + *p + *p + *p;
	  if(*p) {
	    psnext->push_back(p);
	  }
	}
      }
      else {
	for(int * p : *ps) {
	  p = pObjs + *p + *p + *p + 1;
	  if(*p) {
	    psnext->push_back(p);
	  }
	}
      }
      for(int * p : *ps) {
	p = pObjs + *p + *p + *p + 2;
	if(*p) {
	  psnext->push_back(p);
	}
      }
      vector<int *> * tmp;
      tmp = ps;
      ps = psnext;
      psnext = tmp;
      if(ps->empty()) {
	break;
      }
    }
    int value = 0;
    if(!ps->empty()) {
      value = *(*ps)[0];
    }
    int valueeval = 0;
    for(int j = 0; j < noutputs; j++) {
      if(outputs[j][i]) {
	valueeval += 1 << j;
      }
    }
    if(value == valueeval) count++;
  }
  delete ps;
  delete psnext;
  free(pObjs);
  
  return (double)count / inputs[0].size();
}

void platest() {
  vector<boost::dynamic_bitset<> > inputs;
  vector<boost::dynamic_bitset<> > outputs;
  pla2pat("a.pla", inputs, outputs);

  vector<boost::dynamic_bitset<> > onsets(inputs.size());
  for(int i = 0; i < inputs[0].size(); i++) {
    bool fzero = 1;
    for(int j = 0; j < outputs.size(); j++) {
      if(outputs[j][i]) {
	fzero = 0;
	break;
      }
    }
    if(fzero) continue;
    for(int j = 0; j < inputs.size(); j++) {
      onsets[j].push_back(inputs[j][i]);
    }
  }

  vector<boost::dynamic_bitset<> > allone(1);
  for(int i = 0; i < onsets[0].size(); i++) {
    allone[0].push_back(1);
  }
  
  pat2pla("b.pla", onsets, allone);
  
  cout << plaeval("b.pla", inputs, outputs) << endl;
  cout << plaeval("d.pla", inputs, outputs) << endl;
  cout << plaeval("e.pla", inputs, outputs) << endl;
  cout << plaeval("f.pla", inputs, outputs) << endl;
}
