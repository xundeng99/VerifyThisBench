# https://github.com/diffblue/cbmc/releases
sudo docker run -it -v $(pwd)/example.c:/example.c diffblue/cbmc:6.5.0
# cprover