This specification of a multi-car elevator system was originally created as part of a project to compare TLA+ to the then-nascent-but-now-defunct Runway formal specification language.
You can see the analysis posted on the TLA+ google group [here](https://groups.google.com/g/tlaplus/c/5Xd8kv288jE/m/IrliJIatBwAJ).

A number of models are provided, along with their approximate execution time (this is of course dependent on computational power):

| Model File                | Execution Time | Liveness Checking |
| ------------------------- | -------------- | ----------------- |
| ElevatorLivenessSmall.cfg | 10 seconds     | Yes               |
| ElevatorSafetyMedium.cfg  | 3 minutes      | No                |
| ElevatorSafetyLarge.cfg   | 10 minutes     | No                |
| ElevatorLivenessLarge.cfg | 11 minutes     | Yes               |

Run these models from the command line as follows:
```
java tlc2.TLC Elevator.tla -config $ConfigName -workers $ThreadCount -lncheck final
```
with `$ConfigName` replaced by one of the file names in the above table and `$ThreadCount` replaced by the number of hardware threads available on your CPU.

