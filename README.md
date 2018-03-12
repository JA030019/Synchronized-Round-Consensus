# Synchronized-Round-Consensus
<br>
UB Distributed System Course Project <br>

Use TLA+ to implement the algotirhnm


Every process broadcasts (to all other processes, including itself) its initial
value vi. In a synchronous network, this can be done in a single "round" of
messages. After this round, each process decides on the minimum value it
received.<br><br>
If no faults occur, this algorithm is correct. In the presence of a crash
fault, however, a problem can arise. In particular, if a process crashes during
a round, some processes may have received its (low) initial value, but others
may not have. (Note that the channels are always assumed to be fault-free;
they deliver messages reliably once a message is put to the channel.)

