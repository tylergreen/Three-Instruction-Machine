USING: tools.test grouping assocs tim arrays ;

! ***********
! Sample Programs
    
{

    [ { 200 } ]
    [ "main" { }
      "S" <evar>
      "K" <evar> <eap>
      "K" <evar> <eap>
      200  <enumb> <eap>
      <sc>
      1array run-prog ] 
    
    [ { 2 } ]
    [ "main" { } "I" <evar> 2 <enumb> <eap> <sc> 1array  run-prog ] 

    [ { 100 } ]
    [ "main" { } 100 <enumb> <sc> 1array run-prog ] 

    [ { 8 } ]
    [ "main" { } "+" <evar> 5 <enumb> <eap> 3 <enumb> <eap> <sc> 1array run-prog ] 

    [ { 100 } ]
    [ "main" { } "K" <evar> 100 <enumb> <eap> "S" <evar> <eap>
      <sc> 1array run-prog ] 
    
    [ { 1002 } ]
    [ "main" { } "+1" <evar> 1001 <enumb> <eap>
      <sc> 1array run-prog ] 


} 2 group [ unit-test ] assoc-each 
