;generate all combiations of 4 elements

(deffacts elements
    (element a)
    (element b)
    (element c)
    (element d)
)

(defrule combinate
    (element ?a)
    (element ?b)
    (element ?c)
    (element ?d)
    
    =>
    
    ( assert(combination ?a ?b ?c ?d))
    

)