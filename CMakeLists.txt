cmake_minimum_required(VERSION 3.8)
project(testproject CXX C)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)

add_executable(bddl main.cpp pla.cpp aig.cpp)
add_executable(sim main2.cpp pla.cpp aig.cpp)
