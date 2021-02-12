source ~/Projects/emsdk/emsdk_env.sh
emcc -std=c++17 -O3 --bind -DUSE_EASTL=0 -o native.js native.cpp
