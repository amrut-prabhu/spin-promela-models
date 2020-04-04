# CS4211 Formal Methods for Software Engineering

## Question 1

### Part 1

Run using:
- iSpin
- Random, with seed = 123
- maximum number of steps = 10000 

State after 10000 steps:
- CM: POST_REVERTING status
- Client 1: POST_REVERTING status
- Client 2: DISCONNECTED status
- Client 3: POST_REVERTING status
- WCP: DISABLED status

### Part 3

Comment the `atomic` nature in lines 217 and 221 of `weather.pml`. 
(under `:: (cm_status == INITIALIZING && id == client_id && req == GET_NEW_WEATHER_RESP) ->`)

Then, check for deadlocks using iSpin "Verification" and the "+ invalid endstates (deadlock)" option. 
It generates an error trail.
This trail can be viewed in `weather-deadlock.pml`.

### Part 4

Run the original code using iSpin "Verification".

Select the `safety` radio button, and check the `+ invalid endstates (deadlock)` option.
It does not find any errors.


## Question 2

### Part 2

Run `spin -M railway.pml` to output the Message Sequence Chart.
