USING: accessors kernel lists math math.order fry ;
IN: tim.stack

TUPLE: stack s push-count max-depth depth ;
: <stack> ( -- stack ) nil 0 0 0 stack boa ;

! **********
! Machine actions -- clearly not turing complete without random access memory store

: spush ( elem stack -- stack )
    [ cons ] change-s
    [ 1 + ] change-push-count 
    [ 1 + ] change-depth
    dup [ max-depth>> ] [ depth>> ] bi max >>max-depth ;
 
: spop ( stack -- stack elem )
    dup nil?
    [ "Empty Stack -- SPOP" throw ]
    [ [ 1 - ] change-depth
      [ uncons ] change-s swap
    ] if ;

: spop-n ( n stack -- popped-seq )
    over '[ _ - ] change-depth 
    swap '[ _ lcut ] change-s drop ;

