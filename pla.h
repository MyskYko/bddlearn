#pragma once

#include <string>
#include <vector>
#include <boost/dynamic_bitset.hpp>

void pla2pat(std::string filename, std::vector<boost::dynamic_bitset<> > & inputs, std::vector<boost::dynamic_bitset<> > & outputs);
void pat2pla(std::string filename, std::vector<boost::dynamic_bitset<> > const & inputs, std::vector<boost::dynamic_bitset<> > const & outputs);

void patunique(std::vector<boost::dynamic_bitset<> > & inputs, std::vector<boost::dynamic_bitset<> > & outputs);

double plaeval(std::string filename, std::vector<boost::dynamic_bitset<> > const & inputs, std::vector<boost::dynamic_bitset<> > const & outputs);

void platest();
