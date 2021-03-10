from algebra import Expr, ScalPow, Mult,  Plus
from algebra import Associative,Commutative,Identity,Cummulative,NullElement
from algebra import is_scalar, is_number,is_not_number, prod

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

def _check_tensor(expr): 
    try:   
        return expr.is_tensor
    except AttributeError: 
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
    
    def letters_used(self):
        if isinstance(self,MultTensors):
            Scal_terms = self.get_args_Scalar(notNum=True)
            tens_terms = self.get_args_tensors()
            letters_base=list(map(lambda x:x.get_name().lower(),tens_terms))
            letters_ind=list(self.get_indices(names=True))
            return letters_base + letters_ind

        elif isinstance(self,Tensor): 
            letters_ind=list(self.get_indices(names=True))
            return [self.name.lower()] + letters_ind

    def histogram_letters(self): 
        #dejo list_strs por si despues necesito modificar 
        # esta funcion a  histogram_letters(self,list_strs)
        list_strs = self.letters_used()
        d = dict()
        for c in list_strs:
            d[c] = d.get(c, 0) + 1
        return d            


    def valid_index_structure(self): 
        #preguntar
        if max(self.histogram_letters().values()) > 3:
            raise TypeError('Tensors with invalid index structure.')


class Contraction(ValidStructure):

    def _type_letters_used(self):
        #problema si en used hay grek and latin letts 
        used = self.letters_used()
        def is_latin(letter):
            return letter in latinletts
        return latinletts if all(map(is_latin,used)) else grekkletts
    
    def letters_available(self):
        used = self.letters_used()
        letts = self._type_letters_used()
        available = letts.symmetric_difference(set(used))
        return list(available)

    def _quantity_ind_for_term(self):
        if not isinstance(self,MultTensors):
            return [(0,len(self.get_indices()))]
        args = self.get_args_tensors()
        terms = []
        for i in range(len(args)):
                terms.append((i,len(args[i].get_indices())))
        return terms 
    
    def _position_indices(self,notfree=False,free=False,mult_tensor=False):
        """
        (ind,pos_general, by_term)
        """
        termsForpos = self._quantity_ind_for_term() 
        inds = self.get_indices()
        ind_pos = []
        count = 0  
        for i in range(len(inds)):
            print(i,termsForpos,count,inds[i],inds,termsForpos[count][1] - (i+1),"a")
            print(termsForpos[count],"b")
            ind_pos.append((inds[i],i,termsForpos[count][0]))
            print(ind_pos,"c")
            if termsForpos[count][1] - (i+1) == 0 :
                count += 1
        def order_tuple(t):
             return (t[0].get_name(),t[1],t[2])
        ind_pos.sort(key=order_tuple)
        print(ind_pos,"d")
        indsContracted = [f for f in ind_pos if f[0].position==2]
        notFreeinds= [f for f in ind_pos if f[0].position!=2]
        def decision():
            return notFreeinds if notfree else indsContracted
        return decision() if notfree or free  else ind_pos


    
    def contraction(self,mult_tensor=False): 
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
        print(ordered)
        #if not mult_tensor :
        new_inds= tuple(f[0] for f in ordered)
        self.indices= new_inds
        #else:
        #    new_args=[]




        


class Tensor(Expr,Contraction):
    """
    falta: 
    def latex(self)
    
    agregar coordenadas 

    """

    def __init__(self,name,*indices, coordinate = [] ):
        self.name = name
        self.coordinate = coordinate
        self.indices = indices
        self.contraction()
        self.valid_index_structure()
        self.args = (self.name,self.not_free_index())
        self._mhash= None 
        self.scalar = self.is_scalar()
        self.is_tensor = True 
        
    def set_coordinates(self, coordinates):
        self.coordinates = coordinates

    def get_indices(self,names=False):
        inds= tuple(map(lambda x:x.get_name(),self.indices))
        return inds if names else self.indices  

    def __repr__(self):
        name = self.name
        inds = self.indices
        return  self.indices[0] if len(inds) == 1 else name + repr(inds)

    def is_scalar(self):
        inds = self.get_indices()
        if len(inds)==0 or len(self.not_free_index())==0 :
            return True
        return False  

    def not_free_index(self): 
        return tuple(f for f in self.get_indices() if f.position != 2)


    def is_contracted(self):
        for ind in self.get_indices():
            return True if ind.get_position() == 2 else False 
                
    def get_name(self):
        return self.name
                

class MultTensors(Tensor,Associative, Commutative, Identity, Cummulative, 
              NullElement):
    # Associative, Commutative, Identity, Cummulative, 
    #NullElement
    """
    no olvidar que falta implementar class metric 
    que me sube y baja los indices, esto es importante para comparar 
    multtensors ejemplo: 
    R(^mu _nu) = metric(Çbeta Çbeta)* R(^mu _nu Çbeta Çbeta)   
    """
  
    def __new__(cls, *args):
        instance = super(MultTensors, cls).__new__(cls)
        instance._identity_ = 1
        instance._null_ = 0
        instance.args  = args
        instance.make_associative()
        if instance.is_null():
            return 0
        instance.contraction(mult_tensor=True)    
        instance.simplify(ScalPow, lambda a, b: a + b,
                                instance._separate_exp,tensors=True)
        instance.ignore_identity()
        instance.make_commutative(tensors=True)
        return instance
        
    def __init__(self,*args): 
        self._mhash=None

    #def __repr__(self):
    #    s = [self._separate_exp(a) for a in self.args]
    #    numer = ''
    #    denom = ''
    # 
    #    for p, b in s:
    #
    #        if isinstance(b,Plus): 
    #            b_str = '(' + repr(b) + ')' 
    #        elif b == -1 :
    #            b_str = "-" 
    #        else:
    #            b_str = str(b) if is_number(b) else repr(b)           
    #        if is_number(p) and p < 0:
    #            if p == -1:
    #                denom += b_str
    #            else:
    #                p_str = str(-p)
    #                denom += ' ' + b_str + '^' + p_str
    #        else:
    #            if p == 1:
    #                numer += ' ' + b_str
    #            else:
    #                p_str = str(p) if is_number(p) else repr(p)
    #                numer += ' ' + b_str + '^' + p_str
    #
    #    if len(numer) == 0:
    #        numer = str(1)
    #    else:
    #        numer = numer[1:]
    #
    #    if len(denom) == 0:
    #        return numer
    #    else:
    #        return '(' + numer + '/(' + denom + '))' 

    def __repr__(self):
        return '*'.join(str(arg) for arg in self.args)    

    def _separate_exp(self, term):
        return Mult._separate_exp(self, term )
    
    def _number_version(self, *args):
        return prod(args)

    def get_args_Scalar(self,notNum=False):
        args = [f for f in self.args if is_scalar(f) and not _check_tensor(f)]
        notNum_arg = tuple(filter(is_not_number, args))
        return notNum_arg if notNum else tuple(args)

    def get_args_tensors(self,scalars=False,others=False):
        args=[f for f in self.args if _check_tensor(f)]
        scalterms = tuple(filter(is_scalar, args))
        tensNotFreeind = [f for f in args if not f in scalterms]
        def decision():
            return scalterms if scalars else tensNotFreeind
        return decision() if scalars or others  else args


    def get_indices(self,names=False):
        terms = self.get_args_tensors()
        inds = []
        for i in range(len(terms)): 
            inds.extend(terms[i].get_indices())
        str_ind= tuple(map(lambda x:x.get_name(),inds))
        return str_ind if names else tuple(inds)





            