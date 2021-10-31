---- MODULE Twirp ----
(*
This is a simple specification of Responses for 
the Twirp Wire Protocol (v7)
https://twitchtv.github.io/twirp/docs/spec_v7.html
*)

EXTENDS TLC
VARIABLES response

vars == <<response>>

CodeToStatus == [
    canceled            |-> 408,
    unknown             |-> 500,
    invalid_argument    |-> 400,
    malformed           |-> 400,
    deadline_exceeded   |-> 408,
    not_found           |-> 404,
    bad_route           |-> 404,
    already_exists      |-> 409,
    permission_denied   |-> 403,
    unauthenticated     |-> 401,
    resource_exhausted  |-> 429,
    failed_precondition |-> 412,
    aborted             |-> 409,
    out_of_range        |-> 400,
    unimplemented       |-> 501,
    internal            |-> 500,
    unavailable         |-> 503,
    dataloss            |-> 500
]

ErrorStatuses == { CodeToStatus[k] : k \in DOMAIN CodeToStatus }

IncompleteStatus == 0
SuccessfulStatus == 200
PossibleStatuses == SuccessfulStatus \union ErrorStatuses

IsSuccessful == response.status = SuccessfulStatus

TypeOK == response.status \in {
    IncompleteStatus, 
    SuccessfulStatus, 
    400, 401, 403, 404, 408, 409, 412, 429, 500, 501, 503
}

Success(body) ==
    /\ response.status = IncompleteStatus
    /\ response' = [status |-> SuccessfulStatus, body |-> body]

SpecificError(code) ==
    /\ response.status = IncompleteStatus
    /\ response' = [
        status |-> CodeToStatus[code],
        data |-> [code |-> code]]

Error == \E code \in DOMAIN CodeToStatus : SpecificError(code)

Init == response = [status |-> IncompleteStatus]

Next == Success("") \/ Error

Done == response.status # IncompleteStatus

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ WF_vars(Next) \* Use Weak Fairness to prevent stuttering since we can assume that some response will be returned even if the server crashes
----
Prop == <>[]Done
====
