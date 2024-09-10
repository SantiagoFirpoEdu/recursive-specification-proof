theory SizeProperties
    imports Main
begin
    primrec size :: "nat List => nat" where
        base: "size [] = 0" |
        recursive_step: "size h:list = Suc (size list)"
        
end