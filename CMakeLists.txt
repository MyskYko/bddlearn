cmake_minimum_required(VERSION 3.8)
project(testproject CXX C)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
add_compile_options(-g -O3)

add_subdirectory(mockturtle)

add_executable(lbdd main.cpp pla.cpp)
target_link_libraries(lbdd mockturtle)
