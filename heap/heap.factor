USING: accessors assocs kernel lists lists.lazy locals math sequences ;
IN: tim.heap


! *************
! Heap for simple machines


TUPLE: heap size addrs table ;

! distinct address
SINGLETON: hnull 

: <heap> ( -- heap )
    0
    1 lfrom
    H{ } clone
    heap boa ;

:: halloc ( heap obj -- addr )
    [let | next [ heap addrs>> car ]
           free [ heap addrs>> cdr ]
           table [ heap table>> ] |
        obj next table set-at
        heap [ 1 + ] change-size
        [ uncons ] change-addrs drop
    ] ;

: hupdate ( obj addr heap -- ) table>> set-at ;

: hfree ( addr heap -- ) table>> delete-at ;

:: hlookup ( addr heap -- obj )
    addr heap table>> at
    [ "Addr Not found" throw ] unless* ;



    
