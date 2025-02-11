%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                Generic EVM super compilation 
% The max number of stack spots available is denoted by n
% The max number of operations (or steps) performed is denoted by s
% 
% Operations include:
%  POP    pop the top the stack (-1: i.e.,the stack loses one element) (can it be null?**)
%  NOP    do nothing (=)
%  DUP    push the term in the position given by the argument onto the top of stack (+1)
%         possible argument values are 1..16 (or n if n<16)
%  SWAP   swap the term in the position given by the argument+1 with the one on top of stack (=)
%         possible argument values are 1..16 (or n-1 if n<=16) 
%  PUSH   push an argument onto the top of the stack (+1)
%  ZERO   adds an element at the top of the stack, similar to PUSH (+1) 
%         done at least once; common zeroary operations are ADDRESS and??
%  UNARY  do something to the element at the top of the stack (=) 
%         done exactly once; common unary operations include NOT and SLOAD
%  BINARY pop the term at the top and use it to modify the second one (-1) 
%         done exactly once; common binary operations include AND, OR and SHL 
%         (the first two are commutative)
%  STOR   Stores the second argument on the address provided by the first (-2)
%         done exactly once;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% PARAMETERS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
enum TERM; % the different data terms that can appear in the stack; must include null
TERM: null; % specific representation for the null term 

int: s; % max number of steps (operations) allowed
set of int: STEP0 = 0..s; % step index for the stack states (must include the initial state)
set of int: STEP = 1..s; % step index for everything else (do not include the initial state)

int: n; % max stack size available
int: min; %min number of instructions ensured to be needed

set of int: STACK = 1..n; % index for most arrays of decision variables

% start/end state of the stack, where first position is the top and nulls are omitted
array[int] of TERM: startstack;
array[int] of TERM: endstack;

% allowed operations grouped by zero/unary/binary/push/pop/nop/dup/swap (last two indexed by arg position)
% note that the OPCODE implicitly gives the arguments of the operation if any
enum ZEROARYOP; % zero ary operations
array[ZEROARYOP] of TERM: zeroout;
array[ZEROARYOP] of int: zerogas;
array[ZEROARYOP] of int: zerosz;
array[ZEROARYOP] of int: zerolb;
array[ZEROARYOP] of int: zeroub;
enum UNARYOP;  % unary operations
array[UNARYOP] of TERM: unin;  % unary argument required on top of stack (null if dummy)
array[UNARYOP] of TERM: unout; % output of unary operation (null if dummy)
array[UNARYOP] of int: ungas; % gas required for unary operation (0 if dummy)
array[UNARYOP] of int: unsz; % size (bytes) for unary operation (0 if dummy)
array[UNARYOP] of int: unlb;
array[UNARYOP] of int: unub;
enum BINARYOP; % binary operations
array[BINARYOP] of TERM: binin1;  % binary argument required on top of stack (null if dummy)
array[BINARYOP] of TERM: binin2;  % binary argument required on second top stack (null if dummy)
array[BINARYOP] of TERM: binout;  % output of binary operation (null if dummy)
array[BINARYOP] of bool: bincomm; % true if binary operation is commutative (false if dummy)
array[BINARYOP] of int: bingas; % gas required for binary operation (0 if dummy)
array[BINARYOP] of int: binsz; % size (bytes) for binary operation (0 if dummy)
array[BINARYOP] of int: binlb;
array[BINARYOP] of int: binub;
enum PUSHOP;   % push operations
array[PUSHOP] of TERM: pushout;  % output of push operation
array[PUSHOP] of int: pushgas; % gas required for push operation
array[PUSHOP] of int: pushsz; % size (bytes) for push operation
array[PUSHOP] of int: pushlb;
array[PUSHOP] of int: pushub;
enum STOROP; % store operations
array[STOROP] of TERM: storin1;  % store argument required on top of stack (null if dummy)
array[STOROP] of TERM: storin2;  % store argument required on second top stack (null if dummy)
array[STOROP] of int: storlb;
array[STOROP] of int: storub;

%
int: dl = min(n,16);   % dup limit is at most 16
int: sl = min(max(n-1,1),16); % swap limit is at most 16, and at least max(n-1,1) since it indexes from 1
% enumeration of all possible operations for the instance
enum OPCODE = Z(ZEROARYOP) ++ U(UNARYOP) ++ B(BINARYOP) ++ P(PUSHOP) ++ S(STOROP) ++ DUP(1..dl) ++ SWAP(1..sl) ++ { POP, NOP };

% precedences arising from store/load memory operations (only used if both included)
array[int] of OPCODE: before;
array[int] of OPCODE: after;

% different kinds of data (output term, size and gas) for each op in OPCODE
array[OPCODE] of TERM: opout = array1d(OPCODE,zeroout ++ unout ++ binout ++ pushout ++ [ null | i in STOROP ] ++ [ null | i in 1..dl+sl +2]);
array[OPCODE] of int: opsz = array1d(OPCODE,zerosz ++ unsz ++ binsz ++ pushsz ++ [1 | i in STOROP] ++ [ 1 | i in 1..dl+sl ] ++ [1, 0]);
array[OPCODE] of int: opgas = array1d(OPCODE,zerogas ++ ungas ++ bingas ++ pushgas ++ [3 | i in STOROP ] ++ [ 3 | i in 1..dl+sl ] ++ [2,0]);

%any: origsol;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%% FUNCTIONALLY DEPENDENT PARAMETERS %%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%

% set of dummy operations i.e., ZERO/UNARY/BINARY/PUSH/STOR ops with null as output
% (or input if they have no output) arguments.
set of  OPCODE: dummyop = ({ Z(z) | z in ZEROARYOP where zeroout[z] = null } union
                           { U(u) | u in UNARYOP where unout[u] = null } union
                           { B(b) | b in BINARYOP where binout[b] = null } union
                           { P(p) | p in PUSHOP where pushout[p] = null } union
                           { S(r) | r in STOROP where storin1[r] = null });

% set of real operations i.e., those that are not dummy
set of  OPCODE: realop =  OPCODE diff dummyop;
constraint trace(show(realop) ++ "\n",true);

% set of opcodes that must appear exactly once
set of OPCODE: exactly_once_op =  (realop intersect
                                  (U(UNARYOP) union B(BINARYOP) union S(STOROP)
                                   union { P(p) | p in PUSHOP where pushsz[p] >= 3 } ));

% set of opcodes that must occur at least once: same as exactly_once_op + ZEROARYOPs + all PUSHOPs (not just those with size >=3)
set of OPCODE: atleast_once_op =  (realop intersect (Z(ZEROARYOP) union U(UNARYOP) union B(BINARYOP) union  P(PUSHOP) union S(STOROP)));

% maps each term to the number of times it is used by an operartion or by the final (end) stack
array[TERM] of int: uses = [ sum(u in UNARYOP)(unin[u] = t) +
                             sum(b in BINARYOP)(binin1[b] = t) + sum(b in BINARYOP)(binin2[b] = t) +
                             sum(r in STOROP)(storin1[r] = t) + sum(r in STOROP)(storin2[r] = t) +
                             sum(i in index_set(endstack))(endstack[i] = t)
                           | t in TERM ];
constraint trace("uses: " ++ show(uses) ++ "\n",true);

% set of non-null terms that are unused
set of TERM: unused = { t | t in TERM where uses[t] = 0 } diff { null };

% set of opcodes that create at least one non-null term
set of OPCODE: creator_op =  (realop intersect (Z(ZEROARYOP) union U(UNARYOP) union B(BINARYOP) union P(PUSHOP)));

% maps each opcode to the term it creates
array[OPCODE] of TERM: creates = array1d(OPCODE, zeroout ++ unout ++ binout ++ pushout ++ [ null | u in STOROP] ++ [ null | i in 1..dl+sl+2 ]);

% maps each term to either the opcode in ZEROARY/UNARY/BINARY/PUSH that creates it, or to NOP
% --- if several opcodes in ZEROARY/UNARY/BINARY/PUSH create it (can happen?**), arg_max returns the later one (break ties)
% --- Shouldnt be possible for two opcodes to create something, the arg_max returns the first creator in this case!
array[TERM] of OPCODE: creator = array1d(TERM,
      [ let {int: i = arg_max([creates[o]=t| o in Z(ZEROARYOP) ++ U(UNARYOP) ++ B(BINARYOP) ++ P(PUSHOP) ] ++ [true])} in
        if i > card(ZEROARYOP) + card(UNARYOP) + card(BINARYOP) + card(PUSHOP) then NOP else to_enum(OPCODE,i) endif
      | t in TERM ]);
constraint trace("creates: "++show(creates) ++ "\n",true);
constraint trace("creator: "++show([creator[creates[o]] | o in OPCODE where creates[o]!= null]) ++ "\n",true);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% MAIN VARIABLES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% These two are the main ones
array[STEP0,STACK] of var TERM: stack; % term in each stack location at each step including the initial one (step 0)
array[STEP] of var OPCODE: op;  % operation at each (not initial) step

% This one is used for precedence constraints
array[OPCODE] of var STEP0: first; % first time an op occurs as a setp (otherwise, step = 0);
% This one is used for the main objective value
var STEP: length;  % number of operations that will be performed

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%%%% DIRECT PRECEDENCE CONSTRAINTS (resulting from memory load/stores)
constraint forall(i in index_set(before))(first[before[i]] < first[after[i]]);

%%%% ENSURE WE ARE ABOVE THE min Number of instructions
constraint length >= min;

%%%% ENSURE DUMMY OPCODES NEVER OCCUR AS STEPS
constraint forall(i in STEP)(op[i] in realop);

%%%%% SET VALUES OF THE INITIAL AND END STATES FOR THE STACK
% The start state corresponds to step 0, and the end to step s. For both states
% we may need to add nulls (we allowed them to be shorter, to simplify user input)
% The end state will be duplicated backwards until the state at step length
constraint stack[0,..] = startstack ++ [ null | i in 1..n-length(startstack)];
constraint stack[s,..] = endstack ++ [ null | i in 1..n-length(endstack)];

%%%%% CONNECT PRE-POST VALUES OF THE STACK AFTER EACH OPERATION
% join the stacks before and after each operation by means of the step predicate
constraint forall(i in STEP)(step(stack[i-1,..], op[i], stack[i,..]));

% enforce a single step of the relations between stack pre and post given real opcode and argument
predicate step(array[STACK] of var TERM: pre, var OPCODE: o, array[STACK] of var TERM: post) =
     if o = NOP then % stack is unchanged
        post = pre
     elseif o = POP then
        post = pre[2..n] ++ [ null ] % first element disappears; null added at the back
     elseif o in Z(ZEROARYOP) then
        pre[n] = null /\ % stack has space
        post[2..n] = array1d(2..n,pre[1..n-1]) /\ % elements in the old stack are pushed down
        post[1] = zeroout[Z^-1(o)] % output becomes the top
     elseif o in U(UNARYOP) then
        pre[1] = unin[U^-1(o)] /\ % required argument is at the top
        post[1] = unout[U^-1(o)] /\ % output becomes the top
        post[2..n] = array1d(2..n,pre[2..n]) % all but the top is unchanged
     elseif o in B(BINARYOP) then
        post[2..n] = array1d(2..n,pre[3..n] ++ [ null ]) /\ % all but the top is unchanged
        post[1] = binout[B^-1(o)] /\ % output becomes the top
        let { var TERM: arg1 = binin1[B^-1(o)],    % get the two arguments
              var TERM: arg2 = binin2[B^-1(o)] } in
        if bincomm[B^-1(o)]  % if commutative
        then pre[1] = arg1 /\ pre[2] = arg2 \/ pre[1] = arg2 /\ pre[2] = arg1 % one of the 2 orders enforced
        else pre[1] = arg1 /\ pre[2] = arg2 endif % first argument must be the one at the top
     elseif o in P(PUSHOP) then %PUSHOP COULD BE MERGED WITH ZEROARY
        pre[n] = null /\ % stack has space
        post[2..n] = array1d(2..n,pre[1..n-1]) /\ % elements in the old stack are pushed down
        post[1] = pushout[P^-1(o)] % output becomes the top
     elseif o in S(STOROP) then
        pre[1] = storin1[S^-1(o)] /\ pre[2] = storin2[S^-1(o)] /\  % required two arguments at the top
        post = pre[3..n] ++ [ null, null ] % first 2 elements disappear; 2 nulls added at the back
     elseif o in SWAP(1..sl) then
          let { var STACK: a = SWAP^-1(o) + 1, % recall that swapK swaps with position K+1
                var TERM: t = pre[a] } in  % find the term to be swapped
          post[1] = t /\ t != null /\ % first argument must be the one at the top and not be null
          forall(i in STACK where i > 1)
                (post[i] = if i = a then pre[1] else pre[i] endif) % stack unchanged except first and ith swapped
     elseif o in DUP(1..dl) then
          let { var TERM: t = pre[DUP^-1(o)] } in % find the term to be duplicated
          post[1] = t /\ t != null /\ % output is not null and becomes top
          pre[n] = null /\ % stack has space
          post[2..n] = array1d(2..n,pre[1..n-1]) % elements in the old stack are pushed down
     else
          false % no other operations encoded
     endif;

%%%%% NOPS at the end
% operations after the max length must be nops and they are the only nops performed
% Corresponds to old redundant constraint (e) in the CAV paper
constraint forall(i in STEP)(i > length <-> op[i] = NOP);

%%%%% WE ASSUME SOME OPCODES MUST APPEAR EXACTLY ONCE (ALMOST ALWAYS DOMINANCE RULE)
% This is the case for non-dummy UNARY/BINARY/STOR operations, and any PUSHOP whose
% size is >=3 (as it is then better to compute their value). Note that this constraint is
% not redundant because while it implied by the length optimisation (repeating an
% op makes objective worse), so it is not for others.
% Corresponds to a combination of old redundant and non-optimal rules (a) and (b) in CAV paper

% Enforces the step i of each operation o to be the same as first[o], and o cannot appear before
% or after first[o].
constraint forall(o in exactly_once_op)
                  (forall(i in STEP)((op[i] = o -> i = first[o]) /\
                                     (first[o] < i -> op[i] != o)  /\ (first[o] > i -> op[i] != o )));

%%%%% CONNECT THE FIRST OCCURRENCE OF EACH NON-DUMMY UNARY/BINARY/PUSH/STORE OP WITH THE OP MAPPED TO THAT STEP
% no need to do it for DUP/SWAP/POP/NOP because this is only used to enforce "exactly once" and dependencies
% non-dummy checked by means of oput[o]!= null for UNARY/BINARY/PUSH ops and storin1[r] != null for STORE
% Corresponds to a old redundant rule (b) in CAV paper
constraint forall(o in Z(ZEROARYOP) union U(UNARYOP) union B(BINARYOP) union P(PUSHOP) union S(STOROP)
                  where o in realop)
                 (op[first[o]] = o);

% set first[o] to dummy value 0 for useless ops and those of POP/DUP/NOP/SWAP (all have opout[o]= null)
constraint forall(o in dummyop union DUP(1..dl) union SWAP(1..sl) union { POP, NOP })
                 (if opout[o] = null then first[o] = 0 endif);

%%%%% ENFORCE THE INPUT LOWER/UPPER BOUNDS TO THE POSITON OF EVERY OPCODE
constraint forall(z in ZEROARYOP where Z(z) in realop)
                 (first[Z(z)] >= zerolb[z]
                  /\
                  first[Z(z)] + lcount[Z(z)] -1 <= zeroub[z]
                  );
constraint forall(u in UNARYOP where U(u) in realop)
                 (first[U(u)] >= unlb[u]
                  /\
                  first[U(u)] <= unub[u]
                  );
constraint forall(b in BINARYOP where B(b) in realop)
                 (first[B(b)] >= binlb[b]
                  /\
                 first[B(b)] <= binub[b]
                  );
constraint forall(p in PUSHOP where P(p) in realop)
                 (first[P(p)] >= pushlb[p]
                  /\
                 first[P(p)] <= pushub[p]
                  );
constraint forall(r in STOROP where S(r) in realop)
                 (first[S(r)] >= storlb[r]
                  /\
                 first[S(r)] <= storub[r]
                  );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% SIMPLE REDUNDANT CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%

%%%%% NULL EXTENSIONS
% null extends to the right, above and below
constraint forall(i in STEP0, j in 1..n-1)(stack[i,j] = null -> stack[i,j+1] = null);
constraint forall(i in 0..s-1, j in 1..n-1)(stack[i,j] = null -> stack[i+1,j+1] = null);
% the instruction after can have at most 2 less nulls (2 because STOROPs)
constraint
           if realop intersect S(STOROP) = {} then
              forall(i in STEP, j in 1..n-1)(stack[i,j] = null -> stack[i-1,j+1] = null)
           else
              forall(i in STEP, j in 1..n-2)(stack[i,j] = null -> stack[i-1,j+2] = null)
           endif;

%%%%% NOP EXTENSIONS
% NOP extends downwards
% Corresponds to old redundant constraint (e) in CAV paper
constraint forall(i in 1..s-1)(op[i] = NOP -> op[i+1] = NOP);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% REDUNDANT BOUNDS CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%

%%%%% LOWER BOUND ON LENGTH
include "globals.mzn";
% Lower bound of length (i.e., number of opcode occurrences) is the number of ops that occur at least
% once, plus the number of unused non-null terms (as they must be popped)
opt bool: length_bound;
constraint if absent(length_bound) then length >= card(atleast_once_op) + card(unused) endif;

%%%%% LOWER/UPPER BOUND ON THE NUMBER OF OCURRENCES OF EACH OPCODE
% maps each opcode to the lower bound on its number of ocurrences
array[OPCODE] of STEP0: lcount = [ if o in atleast_once_op then 1
                                 elseif o = POP then card(unused) % Non-null unused values must be popped
                                 else 0 endif | o in OPCODE ];

% True if we assume that the max number of DUPs is the number of terms that are used more than once.
opt bool: maxdupassumption = true;

% If maxdupassumption = true, the upper bound on the number of DUPs is number of times a non-null term is
% used, minus the number of terms created either by an op or by the startstack that will be used.
% Otherwise, it is max length minus the ops that must be used at least once minus the number of unused
% -- and thus popped-- terms.
STEP0: maxdups = if occurs(maxdupassumption) then
                  max(0,(sum(uses) - uses[null]) - (card(creator_op) + length(startstack) - card(unused) ))
               else s-card(atleast_once_op) - card(unused) endif ;
               % duplicates can only create extra copies

% upper bound of pops: if maxdupassumption = true, only have to pop what is unused. Otherwise, it is
% max length minus the ops that must be used at least once
STEP0: maxpops = if occurs(maxdupassumption) then card(unused) else s-card(atleast_once_op) endif ;
constraint trace("maxdups = \(maxdups) maxpops = \(maxpops) uses: \(sum(uses)) null = \(uses[null]) unused: \(unused) creates something: \(card(creator_op)) startlength: \(length(startstack))\n",true);

% maps each opcode to the upper bound on its number of occurrences
array[OPCODE] of STEP0: ucount = [ if o in exactly_once_op then 1
                                 elseif o in dummyop then 0
                                 elseif o in Z(ZEROARYOP) then uses[zeroout[Z^-1(o)]]
                                 elseif o in P(PUSHOP) then uses[pushout[P^-1(o)]]
                                 elseif o in DUP(1..dl) then maxdups
                                 elseif o = POP then maxpops
                                 else s-card(atleast_once_op)-card(unused) endif % no limit in this case
                               | o in OPCODE ];
constraint trace("lcount: "++show(lcount) ++ "\n",true);
constraint trace("ucount: "++show(ucount) ++ "\n",true);

%% the actual constraint ensuring the number of times each operator occurs is between lcount[o] and ucount[o]
opt bool: gcc_bounds;
constraint if absent(gcc_bounds) then global_cardinality_low_up(op, OPCODE, lcount, ucount) endif;

%%%%% LOWER/UPPER BOUND ON THE NUMBER OF OCURRENCES OF THE SUM OF SOME OPCODES
% the sum of all DUP occurrences (not just individual ones) cannot be greater than maxdups
constraint sum(i in STEP)(op[i] in DUP(1..dl)) <= maxdups;
%constraint sum(i in STEP)(op[i] in DUP(1..dl) union SWAP(1..sl)) <= s - card(atleast_once_op);

% every reuse of a value created by an exactly once op has to be duplicated
STEP0: mindups = sum(t in TERM where creator[t] in exactly_once_op)(uses[t] - 1);
constraint sum(i in STEP)(op[i] in DUP(1..dl)) >= mindups;

% every reuse of a value created by an at least once op has to be duplicated, repushed, rezerooped
STEP0: minduppzs = sum(t in TERM where creator[t] in creator_op)(uses[t] - 1);
%constraint trace("minduppzs = \(minduppzs);\n", true);
%set of OPCODE: duplicators = Z(ZEROARYOP) union { P(p) | p in PUSHOP where pushsz[p] <= 2 } union DUP(1..dl);
%constraint sum(i in STEP)(op[i] in duplicators) >= minduppzs;
% just to remove a warning, use the following form
constraint sum(i in STEP)(op[i] in Z(ZEROARYOP) \/
                          op[i] in { P(p) | p in PUSHOP where pushsz[p] <= 2 } \/
                          op[i] in DUP(1..dl)) >= minduppzs;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%% REDUNDANT PRECEDENCE CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% If a non-dummy op has an argument that is only created by another op, then we know
% the creator must appear first in the sequence of steps. Explicitely enforce this.
% Corresponds to old redundant constraint (c) in the CAV paper.

% ensure the first occurence of a real UNARY/BINARY/STOR op is after that of the creator
% of its arguments (recall that creator is NOP unless it is in ZEROARY/UNARY/BINARY/PUSH)
constraint forall(u in UNARYOP where U(u) in realop)
                 (if unin[u] in opout then
                     first[U(u)] > first[creator[unin[u]]]
                  endif);
constraint forall(b in BINARYOP where B(b) in realop)
                 (if binin1[b] in opout then
                     first[B(b)] > first[creator[binin1[b]]]
                  endif
                  /\
                  if binin2[b] in opout then
                     first[B(b)] > first[creator[binin2[b]]]
                  endif
                  );
constraint forall(r in STOROP where S(r) in realop)
                 (if storin1[r] in opout then
                     first[S(r)] > first[creator[storin1[r]]]
                  endif
                  /\
                  if storin2[r] in opout then
                     first[S(r)] > first[creator[storin2[r]]]
                  endif
                  );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%% DOMINANCE SHRINKING CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% There are certain situations where two operations can be treated as one (because
% a solution when they are contiguous dominates). In these situations we can shrink
% the search space by forcing the two ops to be contiguous. Intuitively, this occurs
% when an argument is only used once (and its creator is not a NOP), or it is
% created by an op that has no arguments (like PUSH or a ZEROARYOP) and can occur
% anywhere without affecting the objective function (which for PUSH requires its value
% being small). The former are called used_once_nop, the latter zeroary_smpushs. Note
% that the latter is a bit more flexible, as the shrinking can be concatenated for
% several arguments, while the former cannot.
%

% true if the term is used only once and is not created by a NOP
predicate used_once_nop(TERM:t) =
           (uses[t] = 1 /\ creator[t] != NOP);

% set of opcodes created by a ZEROARY or a PUSH with a value of a small size (pushsz[p] <= 2)
set of OPCODE: zeroary_smpushs = Z(ZEROARYOP) union { P(p) | p in PUSHOP where pushsz[p] <= 2 };

% for a non-dummy UNARYOP, if its argument is either created by a zeroary_smpushs, or it is
% used_once_nop, we force the creator to be right before the UNARYOP
opt bool: unary_shrink;
constraint if absent(unary_shrink) then forall(u in UNARYOP where U(u) in realop) %% BUG IF I PUT THE BELOW IN THE WHERE *******
                 (if used_once_nop(unin[u]) \/ creator[unin[u]] in zeroary_smpushs then
                       trace("\(u) -> \(unin[u]):U -> \(creator[unin[u]])\n",
                             op[first[U(u)]-1] = creator[unin[u]])
                  endif
                  ) endif;

% for a non-dummy, commutative binary operation: if both arguments are used_once_nop, we force
% one of the two creators to be right before the BINARYOP (cannot force both because???**)
opt bool: binary_shrink;
constraint if absent(binary_shrink) then forall(b in BINARYOP where B(b) in realop /\ bincomm[b])
                 (if used_once_nop(binin1[b]) /\ used_once_nop(binin2[b]) then
                     trace("\(b) -> {\(creator[binin1[b]]),\(creator[binin2[b]])}\n",
                           op[first[B(b)]-1] in { creator[binin1[b]], creator[binin2[b]] })
                  endif
                  ) endif;

% And: if the first argument is created by a zeroary_smpushs, we force its creator to be right
% before BINARYOP. In this case, if the second argument is also created by a zeroary_smpushs,
% we can force its creator to be right before the creator of argument 1. Also, if the first argument
% is not created by a zeroary_smpushs but the second is, we force the second argument's creator to be right
% before BINARYOP.
constraint if absent(binary_shrink) then forall(b in BINARYOP where B(b) in realop /\ bincomm[b])
           % if first arg is created by a zeroary/smallpushop
           ( if creator[binin1[b]] in zeroary_smpushs then
                 trace("\(b) -> \(binin1[b]):1Z -> \(creator[binin1[b]])\n",
                       op[first[B(b)]-1] = creator[binin1[b]]) /\ % make the creator the previous op
                  % if the second argument is also created by a zeroary/smallpushop (why not if used only once and its creator is not NOP ???**)
                 (if creator[binin2[b]] in zeroary_smpushs then
                     trace("\(b) -> \(binin2[b]):12Z -> \(creator[binin2[b]])\n",
                           op[first[B(b)]-2] = creator[binin2[b]]) % make it the op 2 before
                  endif
                 )
             elseif creator[binin2[b]] in zeroary_smpushs then
                 trace("\(b) -> \(binin2[b]):2Z -> \(creator[binin2[b]])\n",
                       op[first[B(b)]-1] = creator[binin2[b]])  % make its creator the previous op
                  % if the second argument is also used once and its creator is a UNARY/BINARY (i.e., not NOP)
             else true
             endif)
            endif;

% for a non-dummy, non commutative BINARYOP: very smilar to the one above, but
constraint if absent(binary_shrink) then forall(b in BINARYOP where B(b) in realop /\ not bincomm[b])
           % if first arg is created by a zeroary/smallpushop
           ( if creator[binin1[b]] in zeroary_smpushs then
                 trace("\(b) -> \(binin1[b]):1Z -> \(creator[binin1[b]])\n",
                       op[first[B(b)]-1] = creator[binin1[b]]) /\ % make the creator the previous op
                  % if the second argument is also created by a zeroary/smallpushop or used only once and its creator is not NOP
                 (if creator[binin2[b]] in zeroary_smpushs \/ used_once_nop(binin2[b]) then
                     trace("\(b) -> \(binin2[b]):12 -> \(creator[binin2[b]])\n",
                           op[first[B(b)]-2] = creator[binin2[b]]) % make it the op 2 before
                  endif
                 )
             elseif used_once_nop(binin1[b]) then % make it the instruction before
                     trace("\(b) -> \(binin1[b]):1N -> \(creator[binin1[b]])\n",
                           op[first[B(b)]-1] = creator[binin1[b]]) % make it the op 1 before
             else true endif
             ) endif;



% a non-dummy STOROPs is treated identically to a non-dummy, non-commutative BINARYOP
constraint if absent(binary_shrink) then forall(r in STOROP where S(r) in realop)
           % if first arg is created by  zeroary/smallpushop
           ( if creator[storin1[r]] in zeroary_smpushs then
                 trace("\(r) -> \(storin1[r]):1Z -> \(creator[storin1[r]])\n",
                       op[first[S(r)]-1] = creator[storin1[r]]) /\ % make the creator the previous op
                  % if the second argument is also created by a zeroary/smallpushop or used only once and its creator is not NOP
                 (if creator[storin2[r]] in zeroary_smpushs \/ used_once_nop(storin2[r]) then
                     trace("\(r) -> \(storin2[r]):12 -> \(creator[storin2[r]])\n",
                           op[first[S(r)]-2] = creator[storin2[r]]) % make it the op 2 before
                  endif
                 )
             elseif used_once_nop(storin1[r]) then % make it the instruction before
                     trace("\(r) -> \(storin1[r]):1N -> \(creator[storin1[r]])\n",
                           op[first[S(r)]-1] = creator[storin1[r]]) % make it the op 1 before
             else true endif
             ) endif;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% OTHER DOMINANCE CONSTRAINTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%

%%%%% IMMEDIATELY POP UNUSED AT TOP
% compute unused terms and immediately pop them if on top of stack
opt bool: pop_unused;
constraint if absent(pop_unused) then forall(i in STEP)(if stack[i-1,1] in unused then op[i] = POP endif) endif;

% Copying an idea from Alexeys model: too slow for us
% disjunctive reasons for each non-first stack element:
%%  it must come from the line above either 1 earlier or up to 2 later (depending on whether it is STORE)
%% CAREFUL: THE +1 IS MISSING REDO**???
%bool: storesexist = (S(STOROP) intersect realop != {});
%constraint forall(i in STEP, j in 2..n)
%                 (exists(jj in j-1..min(n,j+1+storesexist))(stack[i,j] = stack[i-1,jj])); 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% OBJECTIVE FUNCTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
      
/**** Computations for alternate objectives *****/
var int: totalgas;
constraint totalgas = sum(i in STEP)(opgas[op[i]]);

var int: totalsize;
constraint totalsize = sum(i in STEP)(opsz[op[i]]);

%% calculate size and gas only for operations that dont happen exactly once
array[OPCODE] of int: opsz2 = array1d(OPCODE, zerosz ++ [ 0 | u in UNARYOP] ++ [0 | b in BINARYOP] ++ pushsz ++ [ 0 | r in STOROP] ++ [ 1 | i in 1..dl+sl ] ++ [1, 0]);
array[OPCODE] of int: opgas2 = array1d(OPCODE, zerogas ++ [ 0 | u in UNARYOP] ++ [0 | b in BINARYOP] ++ pushgas ++ [ 0 | r in STOROP ] ++ [ 3 | i in 1..dl+sl ] ++ [2,0]);
var int: totalsize2;
constraint totalsize2 = sum(i in STEP)(opsz2[op[i]]);
var int: totalgas2;
constraint totalgas2 = sum(i in STEP)(opgas2[op[i]]);

/**** end computations for alternate objectives ****/
  
solve 
      %:: int_search(op, input_order, indomain_min)
      %:: int_search([length], input_order, indomain_min) 
      minimize length;
      %minimize totalsize2;
      %minimize totalgas2;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%        OUTPUT               %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
      
array[OPCODE] of string: ops = [ show(o) | o in OPCODE ];
int: maxchar = max( [string_length(ops[o]) | o in OPCODE]);
array[OPCODE] of string: opsj =  [ ops[o] ++ concat([" " | j in 1..maxchar - string_length(ops[o])]) | o in OPCODE ];

array[TERM] of string: ts = [ show(t) | t in TERM ];
int: maxterm = max( [string_length(ts[t]) | t in TERM]);
array[TERM] of string: tsj =  [ ts[t] ++ concat([" " | j in 1..maxterm - string_length(ts[t])]) | t in TERM ];

output [ " " | i in 1..maxchar+4 ] ++ [ tsj[fix(stack[0,j])] ++ if j = n then "\n" else " " endif | j in 1..n];
output [ if j = 0 then show_int(2,i) ++ ":" ++ opsj[fix(op[i])] ++ " " else
                       tsj[fix(stack[i,j])] ++ if j = n then "\n" else " " endif
         endif
       | i in STEP, j in 0..n];
       
output [ "length = \(length);\ngas = \(totalgas);\nbytes = \(totalsize); \nsolution = \(op)\n"];  

 
