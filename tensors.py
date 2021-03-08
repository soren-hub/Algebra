from algebra import Expr 

grekkletts = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta","eta",
        "theta","iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", 
        "sigma","tau", "upsilon", "phi", "chi", "psi", "omega", "digamma",
        "varepsilon","vartheta", "varkappa", "varpi", "varrho","varsigma",
        "varphi" }
        
                
               

latinletts={"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
           "m","n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"}


def indexs(names):
    return tuple(Index(name[0],name[1]) for name in names)


        
def _check_index(expr): 
    try: 
        return expr.is_index
    except AttributeError :
        return False 



class Index(Expr):
    """
        0 -> upper indices 
        1 -> lower index
        2 -> contracted index
    """

    def __new__(cls,name,position):
        if not isinstance(name, str):
            raise TypeError('Name of index must be a string.')
        if not position in [0,1,2]:
            raise ValueError('Position invalid.')
        instance = super(Index, cls).__new__(cls)
        if position == 2: 
            return ContractedIndex(name,position,)
        instance.name = name
        instance.position = position 
        instance.args = (name,position)
        return instance

    
    def __init__(self,name,position):
        self._mhash= None
        self.is_index = True

    def srepr(self):
        pos = self.position 
        name = self.name
        return "_"+name if pos==0 else "^"+name

    def __repr__(self):
        return self.srepr()

    def _letters_used(self): 
        return name 
    
    def get_name(self):
        return self.name
    

    

class ContractedIndex(Expr): 

    def __init__(self,name,position):
        self.name = name
        self.position = position 
        self.args = (name,position)
        self._mhash= None
        self.is_index = True
    
    def srepr(self):
        return "Ç"+self.name
                 
    def __repr__(self):
        return self.srepr()
    
    def is_contracted(self):
        return True 
    
    def get_name(self):
        return self.name
     

def _check_contracted(expr):
    try: 
        return expr.is_contracted()
    except AttributeError: 
        return False 

def _check_index(expr): 
    try: 
        return expr.is_index()
    except AttributeError :
        return False 



def _check_tensor(expr): 
    try: 
        return expr.is_tensor
    except AttributeError :
        return False   

class ValidStructure:

    def histogram_letters(self): 
        list_strs = list(self.get_indices(names=True))
        inds= sorted(list_strs)
        not_repeated = sorted(list(set(inds)))
        count = 0
        record=[]
        for elem in not_repeated:
            for ind in inds:
                if elem == ind: 
                    count += 1 
                else: 
                    record.append((elem,count))
                    count=0
                    break   
        return record            


    def valid_index_structure(self): 
        count = [f[1] for f in self.histogram_letters()]
        if max(count, key=int) > 3:
            raise TypeError('Tensors with invalid index structure.')


class Contraction(ValidStructure):

    def letters_used(self):
        if isinstance(self,Tensor): 
            letters_ind=list(self.get_indices(names=True))
            return [self.name] + letters_ind
    
    def _type_letters_used(self):
        used = self.letters_used()
        def is_latin(letter):
            return letter in latinletts
        return latinletts if all(map(is_latin,used)) else grekkletts
    
    def letters_available(self):
        used = self.letters_used()
        letts = self._type_letters_used()
        available = letts.symmetric_difference(set(used))
        return list(available)
    
    def _position_indices(self,notfree=False,free=False):
        inds=self.get_indices()
        ind_pos = [(inds[i],i) for i in range(len(inds))]         
        def order_tuple(t):
             return (t[0].get_name(),t[1])
        ind_pos.sort(key=order_tuple)
        indsContracted = [f for f in ind_pos if f[0].position==2]
        notFreeinds= [f for f in ind_pos if f[0].position!=2]
        def decision():
            return notFreeinds if notfree else indsContracted
        return decision() if notfree or free  else ind_pos
    
    def contraccion(self): 
        inds_pos = self._position_indices(notfree=True)
        available = self.letters_available()
        ordered = []
        i = 0
        previous = None
        while i < len(inds_pos):
            if previous == None: 
                ordered.append(inds_pos[i])
                previous = inds_pos[i][0]
                i += 1
            elif previous.get_name() == inds_pos[i][0].get_name(): 
                if previous.position != inds_pos[i][0].position:
                    letter = available[0]
                    available.pop(0)
                    new_index = ContractedIndex(letter,2)
                    ordered[i-1] = (new_index,inds_pos[i-1][1])
                    new_ind_pos=(new_index,inds_pos[i][1])
                    ordered.append(new_ind_pos)
                    previous = new_index
                    i += 1
                else:
                    ordered.append(inds_pos[i])
                    previous=inds_pos[i][0]
                    i += 1 
            else:
                ordered.append(inds_pos[i])
                previous = inds_pos[i][0]
                i += 1
        ordered.extend(self._position_indices(free=True))
        ordered.sort(key=lambda tup: tup[1])
        self.indices=tuple(f[0] for f in ordered)

class Tensor(Expr,Contraction):
    """
    falta: 
    def latex(self)
    """

    def __init__(self,name,*indices, coordinate = [] ):
        self.name = name
        self.coordinate = coordinate
        self.indices = indices
        self.contraccion()
        self.valid_index_structure()
        self.args = (self.name,self.indices)
        self._mhash= None 
        self.is_tensor = True 
        
    def set_coordinates(self, coordinates):
        self.coordinates = coordinates
    
    def srepr(self):
        name = self.name
        inds = self.indices
        if len(inds) == 1:
            inds = self.indices[0]
        return name + repr(inds)

    def get_indices(self,names=False):
        inds= tuple(map(lambda x:x.get_name(),self.indices))
        return inds if names else self.indices  

    def __repr__(self):
        return self.srepr()

    def is_scalar(self):
        inds = self.get_indices()
        if len(inds)==0 or all(map(_check_contracted,inds)) :
            return True
        return False  

    def not_free_index(self): 
        return tuple(f for f in self.get_indices() if f.position != 2)


    def is_contracted(self):
        for ind in self.get_indices():
            return True if ind.get_position() == 2 else return False 
                
    def get_name(self):
        return self.name
                


            