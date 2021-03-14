
"""
Created on Sun Mar 7 16:03:23 2021

@authors: Joaquín Rohland and Jorge Noreña  

"""



from algebra import Expr, Scalar, ScalPow, Mult, Plus
from algebra import Associative,Commutative,Identity,Cummulative,NullElement
from algebra import is_scalar, is_number,is_not_number, prod, _distribute_terms
from algebra import expand, derived
grekkletts = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta","eta",
        "theta","iota", "kappa", "lambda", "mu", "nu", "xi", "pi", "rho", 
        "sigma","tau", "upsilon", "phi", "chi", "psi", "omega", "digamma",
        "varepsilon","vartheta", "varkappa", "varpi", "varrho","varsigma",
        "varphi" }

latinletts={"a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
           "m","n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"}


def indexs(names,listvar=[]):
    if len(listvar)!=0: 
        for i in range(len(listvar)): 
            listvar[i]= Index(names[i][0],names[i][1])
    else:
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
            return ContractedIndex(name,position)
        instance.name = name
        instance.position = position 
        instance.args = (name,position)
        return instance

    
    def __init__(self,name,position):
        self._mhash= None
        self.is_index = True


    def __repr__(self):
        pos = self.position 
        name = self.name
        return "_"+name if pos==0 else "^"+name


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
                 
    def __repr__(self):
        return "Ç"+self.name
    
    def is_contracted(self):
        return True 
    
    def get_name(self):
        return self.name
    
    def change_name(self, new_name):
        self.name = new_name

     

def _check_contracted(expr):
    try: 
        return expr.is_contracted()
    except AttributeError: 
        return False 


def _check_tensor(expr): 
    try: 
        return expr.is_tensor
    except AttributeError :
        return False   


class ValidStructure:

    def letters_used(self):
        if isinstance(self,DerivTensors): 
            letters_base = self.base.letters_used()
            letters_ind = list(self.get_indices(deriv=True,names=True))
            return list(letters_base) + letters_ind

        elif isinstance(self,MultTensors):
            Scal_terms = self.get_args_Scalars(notNum=True)
            tens_terms = self.get_args_tensors()
            letters_base = set(map(lambda x:x.get_name().lower(),tens_terms))
            letters_ind = list(self.get_indices(names=True))
            return list(letters_base) + letters_ind

        elif isinstance(self,Tensor): 
            letters_ind=list(self.get_indices(names=True))
            return [self.name.lower()] + letters_ind

    def histogram_letters(self): 
        list_strs = self.letters_used()
        d = dict()
        for c in list_strs:
            d[c] = d.get(c, 0) + 1
        return d            

    def valid_index_structure(self,plustensors=False):
        if plustensors: 
            if not all(map(is_scalar,self.args)): 
                aux = None
                for f in self.args:
                    notFree = f.not_free_index()
                    inds=list(sorted(notFree,key=lambda x:x.get_name()))
                    if aux==None:
                        aux=inds
                    elif aux !=inds :
                        raise TypeError('Trying to add tensors with different'+\
                                                        'index structure.')
        else:
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

    def position_indices(self,notfree=False,contracted=False):
        inds=self.get_indices()
        ind_pos = [(inds[i],i) for i in range(len(inds))]         
        def order_tuple(t):
             return (t[0].get_name(),t[1])
        ind_pos.sort(key=order_tuple)
        indsContracted = [f for f in ind_pos if f[0].position==2]
        notFreeinds= [f for f in ind_pos if f[0].position!=2]
        def decision():
            return notFreeinds if notfree else indsContracted
        return decision() if notfree or contracted  else ind_pos


    def contraction(self,mult_tensor=False): 
        inds_pos = self.position_indices(notfree=True)
        if len(inds_pos) < 1:
            return self 
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
                    letter = available.pop(0)
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
        ind_contracted = self.position_indices(contracted=True)
        if len(ind_contracted)> 0:
            letters = self.histogram_letters()
            i = 0
            previous = None
            while i < len(ind_contracted):
                name = ind_contracted[i][0].get_name()
                if previous == None: 
                    ordered.append(ind_contracted[i])
                    previous = ind_contracted[i][0]
                    i += 1
                elif previous.get_name() == name and letters[name] > 2:
                    letter = available.pop(0)
                    new_index = ContractedIndex(letter,2)
                    ordered[-1] = (new_index,ind_contracted[i-1][1])
                    new_ind_pos=(new_index,ind_contracted[i][1])
                    ordered.append(new_ind_pos)
                    previous = new_index
                    i += 1
                else:
                    ordered.append(ind_contracted[i])
                    previous = ind_contracted[i][0]
                    i += 1
        ordered.sort(key=lambda tup: tup[1])
        new_inds = tuple(f[0] for f in ordered)
        if not mult_tensor:
            self.indices= new_inds
        else :  
            if isinstance(self,MultTensors):
                new_args = list(self.get_args_Scalars())
                old_tens = self.get_args_tensors()
            elif isinstance(self,DerivTensors):
                if isinstance(self.base,MultTensors):
                    new_args = list(self.base.get_args_Scalars())
                    old_tens = self.base.get_args_tensors()
                else: 
                    new_args = []
                    old_tens = [self.base]
            aux = 0
            for term in old_tens:
                name = term.get_name()
                quantity_inds = len(term.get_indices()) + aux 
                inds = new_inds[aux:quantity_inds]
                new_args.append(Tensor(name,*inds)) 
                aux = quantity_inds
            if isinstance(self,MultTensors):
                self.args = new_args
            elif isinstance(self,DerivTensors):
                self.base = MultTensors(*new_args)
                inds_base = len(self.base.get_indices())
                self.indices = new_inds[inds_base:]

        self.valid_index_structure()
        

class Tensor(Expr,Contraction):
    """
    falta: 
    def latex(self)
    
    agregar coordenadas 
    
    cuando se tome una derivada normal se debe introduccir las 
    coordenadas del tensore tambien debo hacerlo si pasa esto ? 
    deriv(Scalar(x)tensor(h,i_0),x )  
    """

    def __init__(self,name,*indices, coordinate = [] ):
        self.name = name
        self.coordinate = coordinate
        self.indices = indices
        self.args = (self.name,self.not_free_index())
        self.contraction()
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
        return  name + repr(inds) if len(inds) > 1 else  name+repr(inds[0])

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
    
    def __mul__(self, other):  
        if isinstance(self,MultTensors) or isinstance(self,Mult): 
            if isinstance(other,MultTensors) or isinstance(other,Mult): 
                return MultTensors(*self.args,*other.args) 
            else:
                return MultTensors(*self.args,other)

        elif isinstance(other,MultTensors) or isinstance(other,Mult):
            if isinstance(self,MultTensors) or isinstance(self,Mult): 
                return MultTensors(*self.args,*other.args) 
            else:
                return MultTensors(self,*other.args)

        elif isinstance(self,Tensor) or isinstance(other,Tensor):
            return MultTensors(self,other)
        
        elif is_scalar(self) and is_scalar(other): 
            return MultTensors(self,other)

        else:
            raise TypeError("unsupported operand type(s) for *: " +\
                                type(self).__name__ + ' and ' +\
                                    type(other).__name__)
    
    def __neg__(self):
        return -1*self
    
    def __rmul__(self, other):
        return self * other

    def __add__(self, other):

        if other == 0:
            return self

        if not _check_tensor(self) or not _check_tensor(other) :
            if _check_tensor(other) and is_scalar(other):
                return PlusTensors(self, other)
            elif _check_tensor(self) and is_scalar(self):
                return PlusTensors(self, other)

            else:
                raise TypeError("unsupported operand type(s) for *: "+\
                                    type(self).__name__ + ' and '+\
                                        type(other).__name__) 

        elif isinstance(self,PlusTensors) :
            if isinstance(other,PlusTensors):
                return PlusTensors(*self.args, *other.args)
            else: 
                return PlusTensors(*self.args, other) 

        elif isinstance(other,PlusTensors):
            return PlusTensors(self,*other.args)

        elif isinstance(self,Tensor) or isinstance(other,Tensor):
            return PlusTensors(self,other)

        else:
            raise TypeError("unsupported operand type(s) for *: " +\
                    type(self).__name__ + ' and ' +\
                        type(other).__name__)

    def __radd__(self, other):
        return  self + other

    def __sub__(self, other):
        return self + -1*other
    
    def __rsub__(self, other):
        return -1*self + other

    def __pow__(self, other):  
        return ScalPow(self, other)
    
    def __rpow__(self,other): 
        return other**self
    
    def __truediv__(self, other):
       if is_scalar(self) and is_scalar(other):
           return MultTensor(ScalPow(other, -1), self)
       else:
           raise TypeError("unsupported operand type(s) for *: " +\
                               type(self).__name__ + ' and ' +\
                                   type(other).__name__)
           
    def __rtruediv__(self, other):
       if is_scalar(self) and is_scalar(other):
           return MultTensor(ScalPow(self, -1), other)
       else:
           raise TypeError("unsupported operand type(s) for *: " +\
                               type(self).__name__ + ' and ' +\
                                   type(other).__name__)
            




#########preguntar por class TensPow 
                

class MultTensors(Tensor,Associative, Commutative, Identity, Cummulative, 
              NullElement):
    # Associative, Commutative, Identity, Cummulative, 
    #NullElement

    #preguntar por las modificaciones al archivo algebra 


    """
    no olvidar que falta implementar class metric 
    que me sube y baja los indices, esto es importante para comparar 
    multtensors ejemplo: 
    R(^mu _nu) = metric(Çbeta Çbeta)* R(^mu _nu Çbeta Çbeta)   
    """
  
    def __new__(cls, *args):
        if len(args) <= 1 :
            return 0 if len(args)==0 else args[0]
        instance = super(MultTensors, cls).__new__(cls)
        instance._identity_ = 1
        instance._null_ = 0
        instance.args  = args
        instance.make_associative_tensors()
        if instance.is_null():
            return 0
        instance.contraction(mult_tensor=True)   
        instance.args = instance.simplify_tens(ScalPow, lambda a, b: a + b,
                                    instance._separate_exp)
        instance.ignore_identity()
        instance.make_commutative(tensors=True)
        if len(instance.args)==1 : return instance.args[0]
        return instance
        
    def __init__(self,*args): 
        self._mhash=None
        self.is_tensor=True
        self.scalar = self.is_scalar()

    def get_name(self):
        #solo para ordenar la suma 
        name = None
        args = self.get_args_tensors()
        for arg in args: 
            if name == None:
                name = arg.get_name()
            else: 
                name += arg.get_name()
        return name
             

    def __repr__(self):
        s = [self._separate_exp(a) for a in self.args]
        numer = ''
        denom = ''
     
        for p, b in s:
    
            if isinstance(b,PlusTensors) or isinstance(b,Plus) : 
                b_str = '(' + repr(b) + ')' 
            elif b == -1 :
                b_str = "-" 
            else:
                b_str = str(b) if is_number(b) else repr(b)           
            if is_number(p) and p < 0:
                if p == -1:
                    denom += b_str
                else:
                    p_str = str(-p)
                    denom += ' ' + b_str + '^' + p_str
            else:
                if p == 1:
                    numer += ' ' + b_str
                else:
                    p_str = str(p) if is_number(p) else repr(p)
                    numer += ' ' + b_str + '^' + p_str
    
        if len(numer) == 0:
            numer = str(1)
        else:
            numer = numer[1:]
    
        if len(denom) == 0:
            return numer
        else:
            return '(' + numer + '/(' + denom + '))' 


    def _separate_exp(self, term):
        return Mult._separate_exp(self, term )
    
    def _number_version(self, *args):
        return prod(args)

    def is_scalar(self): 
        return Tensor.is_scalar(self)

    def get_args_Scalars(self,notNum=False):
        args = [f for f in self.args if is_scalar(f) and not _check_tensor(f)]
        notNum_arg = tuple(filter(is_not_number, args))
        return notNum_arg if notNum else tuple(args)

    def get_args_tensors(self,scalars=False,others=False):
        args=[f for f in self.args if _check_tensor(f)]
        scalterms = tuple(filter(is_scalar, args))
        tensNotFreeind = [f for f in args if not f in scalterms]
        def decision():
            return scalterms if scalars else tuple(tensNotFreeind)
        return decision() if scalars or others  else tuple(args)


    def get_indices(self,names=False):
        terms = self.get_args_tensors()
        inds = []
        for term in terms: 
            inds.extend(term.get_indices())
        str_ind= tuple(map(lambda x:x.get_name(),inds))
        return str_ind if names else tuple(inds)

    def expanded(self):
        terms = list(map(expand,self.args))
        plus_terms = [f.args for f in terms if isinstance(f,PlusTensors)]
        rest_terms = [f for f in terms if not isinstance(f,PlusTensors)]
        left = MultTensors(*rest_terms)
        if len(plus_terms)==0:
            return left
        expand_plus = _distribute_terms(plus_terms)
        rigth = PlusTensors(*expand_plus)
        new_args = list(map(lambda f: left*f,expand_plus)) 
        return PlusTensors(*new_args)
    





class PlusTensors(Expr,ValidStructure,Associative, Commutative, Identity,
                    Cummulative):

    def __new__(cls, *args):
        if len(args) <= 1 :
            return 0 if len(args)==0 else args[0]
        instance = super(PlusTensors, cls).__new__(cls)
        instance._identity_ = 0
        instance.args = args
        instance.make_associative_tensors()
        instance.ignore_identity()
        if len(instance.args)==0: 
            return 0
        if len(instance.args) == 1:
            return instance.args[0]
        instance.valid_index_structure(plustensors=True)
        instance.make_commutative(plustensors=True)
        instance.args=instance.simplify(MultTensors,instance._scalar_version,
                                        instance._separate_scal,instance.args,
                                        sumTens=True)                                      
        if all([is_number(a) for a in instance.args]):
            return sum(args)
        else:
            return instance

    def __init__(self,*args):
        self._mhash = None 
        self.is_tensor = True

    def _separate_scal(self, term):
        if isinstance(term, MultTensors):
            scalars = term.get_args_Scalars()
            if  len(scalars)>0:
                scal = MultTensors(*term.args[:len(scalars)])
                tens = MultTensors(*term.args[len(scalars):])
                return scal, tens
            else: 
                return 1, term
        else:
            return 1, term
        
    def __repr__(self):
        l = [(str(a) if is_number(a) else repr(a)) for a in self.args]
        return ' + '.join(l) 
     
    def _scalar_version(self, *args):
        return Plus(*args)
    
    def get_args_Scalars(self,notNum=False):
        return MultTensors.get_args_Scalars(self,notNum)
        
    def get_args_tensors(self,scalars=False,others=False):
        return MultTensors.get_args_Scalars(self,scalars,others)

    def expanded(self):
        terms = list(map(expand,self.args))
        return PlusTensors(*terms)

#class Metric(Tensor): 



class DerivTensors(Tensor): 
    
    #ver que hacer con base= mult
    
    def __new__(cls,base,*indices, coordinate = []):
        if not _check_tensor(base):
            raise TypeError('DerivTensors should only involve'+\
                                                         'Tensors objects.')
        instance = super(DerivTensors, cls).__new__(cls)
        instance.base=base
        instance.indices = indices
        instance.coordinate = coordinate
        if is_number(instance.base):
            return 0
        if isinstance(instance.base,DerivTensors): 
            instance.indices= instance.indices + instance.base.indices
            instance.base=instance.base.base
            return instance
        elif isinstance(instance.base,PlusTensors):
            return  instance.expanded()
        return instance

    def __init__(self,base,*indices, coordinate = []):
        self.contraction(mult_tensor=True)
        self.args=(self.base,self.not_free_index())
        self._mhash = None
        self.is_tensor = True 
    
    def get_indices(self,deriv=False,names=False):
        inds_deriv = list(self.indices)
        if isinstance(self.base,PlusTensors): 
            inds_base = []
        else:
            inds_base= list(self.base.get_indices())
        all_ind = tuple(inds_base + inds_deriv)
        decision= all_ind if not deriv else tuple(inds_deriv)
        str_ind = tuple(map(lambda x:x.get_name(),decision))
        return decision if not names else str_ind


    def __repr__(self): 
        b_str = str(self.base)
        coo_str = repr(self.coordinate)
        ind = self.indices if len(self.indices)>1 else self.indices[0]
        inds_str = str(ind) 
        return "∂(" + b_str + ',' + inds_str +")" 

    def get_name(self):
        inds_str=self.get_indices(deriv=True)
        base_str=self.base.get_name()
        deriv_str= "∂"+ ','.join(repr(f) for f in inds_str)
        return deriv_str + "("+ base_str +")"
    
    def expanded(self):
        if isinstance(self.base,MultTensors):
            new_terms=[]
            terms = [f for f in self.base.args]
            for i in range(len(terms)): 
                new_element = [e for e in terms]
                inds=self.get_indices(deriv=True)
                new_element[i] = DerivTensors(new_element[i],*inds)
                new_terms.append(MultTensors(*new_element))
            return PlusTensors(*new_terms)
        elif isinstance(self.base,PlusTensors):
            terms = self.base.expanded().args
            inds = self.get_indices(deriv=True)
            new_terms = list(map(lambda x:DerivTensors(x,*inds),terms))
            return PlusTensors(*new_terms)
        else:
            return self 
    