#include <iostream>
#include <sstream>
#include <algorithm>
#include <cassert>

#include "aig.hpp"

unsigned char getnoneofch (std::ifstream & file)
{
  int ch = file.get();
  assert(ch != EOF);
  return ch;
}
unsigned decode (std::ifstream & file)
{
  unsigned x = 0, i = 0;
  unsigned char ch;
  while ((ch = getnoneofch (file)) & 0x80)
    x |= (ch & 0x7f) << (7 * i++);
  return x | (ch << (7 * i));
}
void encode (std::ofstream & file, unsigned x)
{
  unsigned char ch;
  while (x & ~0x7f)
    {
      ch = (x & 0x7f) | 0x80;
      file.put(ch);
      x >>= 7;
    }
  ch = x;
  file.put(ch);
}

void aigman::read(std::string filename) {
  std::ifstream f(filename);
  {
    std::string str;
    getline(f, str);
    std::stringstream ss(str);
    getline(ss, str, ' ');
    assert(str == "aig");
    getline(ss, str, ' ');
    nObjs = stoi(str);
    getline(ss, str, ' ');
    nPis = stoi(str);
    getline(ss, str, ' ');
    nLats = stoi(str);
    getline(ss, str, ' ');
    nPos = stoi(str);
    getline(ss, str, ' ');
    nGates = stoi(str);
    if(!nPos) {
      getline(ss, str, ' ');
      nPos = stoi(str);
      getline(ss, str, ' ');
      assert(str == "0");
    }
    assert(nObjs == nGates + nPis + nLats);
  }

  nObjs++; // constant
  vLis.resize(nLats);
  vLos.resize(nLats);
  vPos.resize(nPos);
  vObjs.resize(nObjs << 1);

  {
    std::string str;
    for(int i = 0; i < nLats; i++) {
      getline(f, str);
      int pos = str.find(" ");
      vLis[i] = stoi(str.substr(0, pos));
      vLos[i] = stoi(str.substr(pos + 1));
    }
  }
  
  {
    std::string str;
    for(int i = 0; i < nPos; i++) {
      getline(f, str);
      vPos[i] = stoi(str);
    }
  }

  for(int i = nPis + nLats + 1; i < nObjs; i++) {
    vObjs[i + i] = i + i - decode(f);
    vObjs[i + i + 1] = vObjs[i + i] - decode(f);
  }

  f.close();
}

int aigman::renumber_rec(int i, std::vector<int> & vObjsNew, int & nObjsNew) {
  if(i <= nPis + nLats) return i;
  if(vValues[i]) return vValues[i];
  int l = renumber_rec(vObjs[i + i] >> 1, vObjsNew, nObjsNew);
  int r = renumber_rec(vObjs[i + i + 1] >> 1, vObjsNew, nObjsNew);
  if(l < r) std::swap(l, r);
  vObjsNew[nObjsNew + nObjsNew] = (l << 1) + (vObjs[i + i] & 1);
  vObjsNew[nObjsNew + nObjsNew + 1] = (r << 1) + (vObjs[i + i + 1] & 1);
  vValues[i] = nObjsNew++;
  return vValues[i];
}

void aigman::renumber() {
  vValues.clear();
  vValues.resize(nObjs);
  int nObjsNew = nPis + nLats + 1;
  std::vector<int> vObjsNew((nObjsNew + nGates) << 1);
  for(int i = 0; i < nLats; i++) {
    int j = vLis[i] >> 1;
    vLis[i] = (renumber_rec(j, vObjsNew, nObjsNew) << 1) + (vLis[i] & 1);
  }
  for(int i = 0; i < nPos; i++) {
    int j = vPos[i] >> 1;
    vPos[i] = (renumber_rec(j, vObjsNew, nObjsNew) << 1) + (vPos[i] & 1);
  }
  vObjs = vObjsNew;
  nObjs = nObjsNew;
  assert(nObjs == 1 + nPis + nLats + nGates);
}

void aigman::write(std::string filename) {
  renumber();
  std::ofstream f(filename);
  f << "aig " << nObjs - 1 << " " << nPis << " " << nLats << " " << nPos << " " << nObjs - nPis -nLats - 1 << std::endl;
  for(int i = 0; i < nLats; i++) {
    f << vLis[i] << " " << vLos[i] << std::endl;
  }
  for(int i = 0; i < nPos; i++) {
    f << vPos[i] << std::endl;
  }
  for(int i = nPis + nLats + 1; i < nObjs; i++) {
    assert(vObjs[i + i] >= vObjs[i + i + 1]);
    encode(f, i + i - vObjs[i + i]);
    encode(f, vObjs[i + i] - vObjs[i + i + 1]);
  }
  f.close();
}

int aigman::getvalue(int i) {
  assert((i >> 1) < nObjs);
  if(i & 1) {
    return vValues[i >> 1] ^ 0xffffffff;
  }
  return vValues[i >> 1];
}

void aigman::simulate(std::vector<int> const & inputs) {
  assert(inputs.size() == nPis + nLats);
  vValues.resize(nObjs);
  vValues[0] = 0; // constant
  for(int i = 0; i < nPis + nLats; i++) {
    vValues[i + 1] = inputs[i];
  }
  for(int i = nPis + nLats + 1; i < nObjs; i++) {
    vValues[i] = getvalue(vObjs[i + i]) & getvalue(vObjs[i + i + 1]);
  }
}

void aigman::supportfanouts_rec(int i) {
  if(i <= nPis + nLats || vValues[i]) return;
  {
    int j = vObjs[i + i] >> 1;
    vvFanouts[j].push_back(i);
    supportfanouts_rec(j);
  }
  {
    int j = vObjs[i + i + 1] >> 1;
    vvFanouts[j].push_back(i);
    supportfanouts_rec(j);
  }
  vValues[i] = 1;
}

void aigman::supportfanouts() {
  vValues.clear();
  vValues.resize(nObjs);
  vvFanouts.clear();
  vvFanouts.resize(nObjs);
  for(int i = 0; i < nLats; i++) {
    int j = vLis[i] >> 1;
    vvFanouts[j].push_back(- i - 1);
    supportfanouts_rec(j);
  }
  for(int i = 0; i < nPos; i++) {
    int j = vPos[i] >> 1;
    vvFanouts[j].push_back(- i - 1 - nLats);
    supportfanouts_rec(j);
  }
}

int aigman::supportlevels() {
  if(vvFanouts.empty()) {
    supportfanouts();
  }
  vValues.clear();
  vValues.resize(nObjs);
  vLevels.resize(nObjs);
  std::vector<int> * cur = new std::vector<int>;
  std::vector<int> * next = new std::vector<int>;
  for(int i = 0; i < nLats; i++) {
    cur->push_back(vLis[i] >> 1);
  }
  for(int i = 0; i < nPos; i++) {
    cur->push_back(vPos[i] >> 1);
  }
  int level = 0;
  while(!cur->empty()) {
    for(int i : *cur) {
      vValues[i] = 1;
      vLevels[i] = level;
      if(i <= nPis + nLats) continue;
      {
	int j = vObjs[i + i] >> 1;
	bool f = 1;
	for(int k : vvFanouts[j]) {
	  if(k < 0) {
	    continue;
	  }
	  if(!vValues[k]) {
	    f = 0;
	    break;
	  }
	}
	if(f) {
	  next->push_back(j);
	}
      }
      {
	int j = vObjs[i + i + 1] >> 1;
	bool f = 1;
	for(int k : vvFanouts[j]) {
	  if(k < 0) {
	    continue;
	  }
	  if(!vValues[k]) {
	    f = 0;
	    break;
	  }
	}
	if(f) {
	  next->push_back(j);
	}
      }
    }
    level++;
    auto tmp = cur;
    cur = next;
    next = tmp;
    next->clear();
  }
  delete cur;
  delete next;
  return level - 1;
}

void aigman::removenode(int i) {
  assert(!vDeads.empty());
  if(i <= nPis + nLats) return;
  if(vDeads[i]) return;
  vDeads[i] = 1;
  nGates--;
  if(vvFanouts.empty()) return;
  assert(vvFanouts[i].empty());
  {
    int j = vObjs[i + i] >> 1;
    auto it = find(vvFanouts[j].begin(), vvFanouts[j].end(), i);
    assert(it != vvFanouts[j].end());
    vvFanouts[j].erase(it);
    if(vvFanouts[j].empty()) {
      removenode(j);
    }
    else if(!vLevels.empty()) {
      vLevels[j] = 0;
      for(int k : vvFanouts[j]) {
	if(k < 0) continue;
	if(vLevels[j] < vLevels[k] + 1) {
	  vLevels[j] = vLevels[k] + 1;
	}
      }
    }
  }
  {
    int j = vObjs[i + i + 1] >> 1;
    auto it = find(vvFanouts[j].begin(), vvFanouts[j].end(), i);
    assert(it != vvFanouts[j].end());
    vvFanouts[j].erase(it);
    if(vvFanouts[j].empty()) {
      removenode(j);
    }
    else if(!vLevels.empty()) {
      vLevels[j] = 0;
      for(int k : vvFanouts[j]) {
	if(k < 0) continue;
	if(vLevels[j] < vLevels[k] + 1) {
	  vLevels[j] = vLevels[k] + 1;
	}
      }
    }
  }
}

void aigman::replacenode(int i, int j, bool prop) {
  assert(i >= 0);
  assert(j >= 0);
  assert(!vDeads.empty());
  assert(!vDeads[i]);
  assert(!vDeads[j >> 1]);
  assert(!vvFanouts.empty());
  std::vector<int> targets = vvFanouts[i];
  if(i == (j >> 1)) {
    if(j & 1) {
      for(int k : vvFanouts[i]) {
	if(k < -nLats) {
	  vPos[- k - 1 - nLats] ^= 1;
	  continue;
	}
	else if(k < 0) {
	  vLis[- k - 1] ^= 1;
	  continue;
	}
	if((vObjs[k + k] >> 1) == i) {
	  vObjs[k + k] ^= 1;
	}
	if((vObjs[k + k + 1] >> 1) == i) {
	  vObjs[k + k + 1] ^= 1;
	}
      }
    }
  }
  else {
    for(int k : vvFanouts[i]) {
      if(k < -nLats) {
	vPos[- k - 1 - nLats] = j ^ (vPos[- k - 1 - nLats] & 1);
      }
      else if(k < 0) {
	vLis[- k - 1] = j ^ (vLis[- k - 1] & 1);
      }
      else {
	if((vObjs[k + k] >> 1) == i) {
	  vObjs[k + k] = j ^ (vObjs[k + k] & 1);
	}
	if((vObjs[k + k + 1] >> 1) == i) {
	  vObjs[k + k + 1] = j ^ (vObjs[k + k + 1] & 1);
	}
	if(!vLevels.empty() && vLevels[j >> 1] < vLevels[k] + 1) {
	  vLevels[j >> 1] = vLevels[k] + 1;
	}
      }
      vvFanouts[j >> 1].push_back(k);
    }
    vvFanouts[i].clear();
    removenode(i);
  }
  
  if(!prop) return;
  
  for(int k : targets) {
    if(k < 0) {
      continue;
    }
    if(vDeads[k]) continue;
    if((vObjs[k + k] >> 1) == (vObjs[k + k + 1] >> 1)) {
      if((vObjs[k + k] & 1) == (vObjs[k + k + 1] & 1)) {
	replacenode(k, 1);
      }
      else {
	replacenode(k, 0);
      }
      continue;
    }
    if(!(vObjs[k + k] >> 1)) {
      if(vObjs[k + k] & 1) {
	replacenode(k, vObjs[k + k + 1]);
      }
      else {
	replacenode(k, 0);
      }
      continue;
    }
    if(!(vObjs[k + k + 1] >> 1)) {
      if(vObjs[k + k + 1] & 1) {
	replacenode(k, vObjs[k + k]);
      }
      else {
	replacenode(k, 0);
      }
    }
  }
}

aigman * aigman::copy() {
  aigman * p = new aigman(nPis, nLats);
  *p = *this;
  return p;
}
void aigman::save(int i) {
  if(backup.size() <= i) {
    backup.resize(i + 1);
  }
  backup[i] = copy();
}

void aigman::load(int i) {
  assert(backup.size() > i);
  aigman * p = backup[i];
  *this = *p;
}

void aigman::markfocone_rec(int i) {
  assert(!vvFanouts.empty());
  if(vValues[i]) return;
  vValues[i] = 1;
  for(int j : vvFanouts[i]) {
    if(j < 0) {
      continue;
    }
    markfocone_rec(j);
  }
}

int aigman::newobj(int i, int j) {
  if(i == 0) return 0;
  if(j == 0) return 0;
  if(i == 1) return j;
  if(j == 1) return i;
  if(i == j) return i;
  if(i >> 1 == j >> 1) return 0;
  if(vObjs.size() < nObjs + nObjs + 2)
    vObjs.resize(nObjs << 2);
  vObjs[nObjs + nObjs] = i;
  vObjs[nObjs + nObjs + 1] = j;
  nGates++;
  return nObjs++ << 1;
}

void aigman::newpo(int i) {
  vPos.push_back(i);
  nPos++;
}

int aigman::newor(int i, int j) {
  int f = newobj(i ^ 1, j ^ 1);
  return f ^ 1;
}

int aigman::newite(int c, int t, int e) {
  int f1 = newobj(c, t);
  int f0 = newobj(c ^ 1, e);
  return newor(f1, f0);
}
