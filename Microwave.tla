\*34567890123456789012345678901234567890123456789012

-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS
  \* Flag for enabling safety check upon starting radiation
  ImplementStartSafety,
  \* Flag for enabling safety check upon opening door
  ImplementOpenDoorSafety

VARIABLES
  \* See TypeOK below for type constraints
  door,
  radiation,
  timeRemaining,
  powerLevel

\* Tuple of all variables
vars == << door, radiation, timeRemaining, powerLevel >>

\* Symbolic names for significant strings
OFF == "off"
ON == "on"
CLOSED == "closed"
OPEN == "open"
LOW == "low"
MEDIUM == "medium"
HIGH == "high"

\* Dynamic type invariant
TypeOK == 
  /\ door \in { CLOSED, OPEN }
  /\ radiation \in { OFF, ON }
  /\ timeRemaining \in Nat
  /\ powerLevel \in { LOW, MEDIUM, HIGH }

MaxTime == 60

\* Valid initial state(s)
Init ==
  /\ door \in { OPEN, CLOSED }
  /\ radiation = OFF
  /\ timeRemaining = 0
  /\ powerLevel = MEDIUM

\* Increment remaining time by one second
IncTime ==
  /\ radiation = OFF
  /\ timeRemaining' = timeRemaining + 1
  /\ timeRemaining' <= MaxTime
  /\ UNCHANGED << door, radiation, powerLevel >>

\* Start radiation and time countdown
Start ==
  /\ radiation = OFF
\* cannot heat if door open
  /\ door = CLOSED
  /\ timeRemaining > 0
  /\ radiation' = ON
  /\ UNCHANGED << door, timeRemaining, powerLevel >>

\* Cancel radiation and reset remaining time
Cancel ==
  /\ radiation' = OFF
  /\ timeRemaining' = 0
  /\ UNCHANGED << door, powerLevel >>

\* Internal clock tick for time countdown
Tick ==
  /\ radiation = ON
  /\ timeRemaining' = timeRemaining - 1
  /\ timeRemaining' >= 0
  /\ IF timeRemaining' = 0 
     THEN radiation' = OFF 
     ELSE UNCHANGED << radiation >>
  /\ UNCHANGED << door, powerLevel >>

\* Open door
OpenDoor ==
  /\ door' = OPEN
\* radiation is always turned off when door open
  /\ radiation' = OFF
  /\ UNCHANGED << timeRemaining, powerLevel >>

\* Close door
CloseDoor ==
  /\ door' = CLOSED
  /\ UNCHANGED << radiation, timeRemaining, powerLevel >>

\* Adjust power levels

SetPowerLow ==
  /\ powerLevel' = LOW
  /\ UNCHANGED << door, radiation, timeRemaining >>

SetPowerMedium ==
  /\ powerLevel' = MEDIUM
  /\ UNCHANGED << door, radiation, timeRemaining >>

SetPowerHigh ==
  /\ powerLevel' = HIGH
  /\ UNCHANGED << door, radiation, timeRemaining >>

Pause ==
  /\ radiation = ON
  /\ radiation' = OFF
  /\ UNCHANGED << door, timeRemaining, powerLevel >>

Resume ==
  /\ radiation = OFF
  /\ door = CLOSED
  /\ timeRemaining > 0
  /\ radiation' = ON
  /\ UNCHANGED << door, timeRemaining, powerLevel >>

Fault_StuckDoor ==
  /\ door' = door  \* Door remains in its current state
  /\ UNCHANGED << radiation, timeRemaining, powerLevel >>

Recover_StuckDoor ==
  /\ door' = CLOSED  \* Forces door to close properly
  /\ UNCHANGED << radiation, timeRemaining, powerLevel >>

\* All valid actions (state transitions)
Next ==
  \/ IncTime
  \/ Start
  \/ Cancel
  \/ OpenDoor
  \/ CloseDoor
  \/ Tick
  \/ SetPowerLow
  \/ SetPowerMedium
  \/ SetPowerHigh
  \/ Pause
  \/ Resume
  \/ Fault_StuckDoor
  \/ Recover_StuckDoor

\* All valid system behaviors starting from the initial state
Spec == Init /\ [][Next]_vars

\* Valid system behaviors with weak fairness to disallow stuttering
\* added additional fairness constraint to prevent permanent radiation
FSpec == Spec /\ WF_vars(Tick) /\ WF_vars(Cancel)

\* Safety check to detect radiation with door open
DoorSafety == door = OPEN => radiation = OFF

\* Temporal check to detect indefinite radiation
HeatLiveness == radiation = ON ~> radiation = OFF

RunsUntilDoneOrInterrupted == 
  [][radiation = ON => radiation' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
    action := "10min"
    action := "1min"
    action := "10sec"
    action := "power"
    action := "timer"
*)

\* DoorSafety == RequireSafety => radiation = ON => door = CLOSED

\* deadlock detection: ensures no action is indefinitely blocked
DeadlockFree ==
  \E act \in {Start, Tick, OpenDoor, CloseDoor, Cancel, SetPowerLow, SetPowerMedium, SetPowerHigh, Pause, Resume} :
    [][act]_vars

\* deadlock prevention: at least one action must be possible
NoDeadlock == <>[] DeadlockFree

\* concurrency
Concurrency ==
  \A m \in 1..MicrowaveCount :
    Next_m == Start \/ Tick \/ OpenDoor \/ CloseDoor \/ Cancel
