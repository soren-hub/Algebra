
"""
Created on Fri Feb 26 22:21:55 2021

@authors: Joaquín Rohland and Jorge Noreña  

"""



import sympy as sp

symbol_dict = {}

def scalars(names):
    return tuple(Scalar(name) for name in names)

def srepr(a):
    try:
        return a.srepr()
    except AttributeError:
        return repr(a)

def sympy(expr):
    try:
        return expr.sympy()
    except AttributeError:
        return expr   
    
def fract(numer, denom):
    if (isinstance(numer, float) and is_number(denom)) or\
        (isinstance(denom, float) and is_number(numer)):
        return numer/denom
    elif not is_scalar(numer) or not is_scalar(denom):
        raise TypeError('Can only divide scalars (or numbers).')
    else:
        return Mult(numer, ScalPow(denom, -1))

def is_sympy_number(tree):
    return isinstance(tree, sp.Float) or isinstance(tree, sp.Integer)

def translate_sympy(tree):
    
    if isinstance(tree, sp.Add):
        if isinstance(tree.args[-1],sp.Order): 
            variable = tree.args[-1].args[0].args[0]
            order_serie = tree.args[-1].args[0].args[1]
            args = [translate_sympy(a) for a in tree.args[:-1]]
            return Serie(args,variable,order_serie)
        else:
            return(Plus(*[translate_sympy(a) for a in tree.args]))
    elif isinstance(tree, sp.Mul):
        return(Mult(*[translate_sympy(a) for a in tree.args]))
    elif isinstance(tree, sp.Pow):
        return ScalPow(*[translate_sympy(a) for a in tree.args]) 
    elif isinstance(tree, sp.Rational):
        return fract(translate_sympy(tree.p), translate_sympy(tree.q))
    elif isinstance(tree, sp.Symbol) or is_sympy_number(tree):
        return symbol_dict[tree]
    elif is_number(tree):
        return tree
    else:
        print('Could not translate:', tree)
    
    
def prod(args):
    res = 1
    for a in args:
        res *= a
    return res

def is_number(n):
    return isinstance(n, int) or isinstance(n, float)    

def is_not_number(n):
    return not (isinstance(n, int) or isinstance(n, float))

def is_scalar(expr):
    try:
        return expr.scalar
    except AttributeError:
        if isinstance(expr, int) or isinstance(expr, float):
            return True
        else:
            return False
        
def expand(exp):
    try:
        return exp.expanded()
    except AttributeError:
        return exp

    
def derived(exp,coordinate):
    try:
        return exp.derived(coordinate)
    except AttributeError:
        return 0
    


    
def _distribute_terms(terms):
    """
    recibe una lista con los elementos de cada suma que haya en una expresion 
    y distribuye los elementos con todos los elementos 
    """
    aux_ind=0
    new_list=[terms[0]]
    while aux_ind < len(terms)-1 : 
        aux_list=[]
        for i in range(len(new_list[aux_ind])):
            for j in range(len(terms[aux_ind+1])):
                new_terms=Mult(new_list[aux_ind][i],terms[aux_ind+1][j])
                aux_list.append(new_terms)
        new_list.append(aux_list)
        aux_ind +=1 
    return new_list[-1]
    

    
class Associative():   
    
    def make_associative(self):    
        new_args = []
        for a in self.args:
            if type(a) == type(self):
                new_args.extend(a.args)
            else:
                new_args.append(a)
        self.args = tuple(new_args)
        
class Commutative():  

    def make_commutative(self):
        constlist = list(filter(is_number, self.args))
        arglist = sorted(list(filter(is_not_number, self.args)), key=hash)
        if len(constlist) > 0:
            number = self._number_version(*constlist)
            arglist.insert(0,number) 
        self.args = tuple(arglist)

class Identity():
    
    def ignore_identity(self):
        self.args = tuple(filter(self._identity_.__ne__, self.args))
    

class NullElement():
    
    def is_null(self):
        return self._null_ in self.args
    
    
class Cummulative():
    
    def simplify(self, repeated, operate, separate):
        previous = None
        c = None
        terms = []
        def key(term):
            ci, t  = separate(term)
            return hash(t)
        args = sorted(self.args, key=key)
        for term in args:
            ci, current = separate(term)
            if current != previous:
                if previous != None:
                    terms.append(repeated(previous, c))
                c = ci
                previous = current
            else:
                c = operate(c, ci)
        terms.append(repeated(previous, c))
        self.args = tuple(terms)
    
    

class Expr:
    def __init__(self):
        self._mhash = None
    
    def __hash__(self):
        h = self._mhash 
        if h is None:
            h = hash((type (self).__name__,) + \
                     tuple (self.args))
            self._mhash = h
        return h
    
    def srepr(self):
        return type(self).__name__ + '(' +\
            ', '.join(srepr(a) for a in self.getargs()) + ')'
            
    def __repr__(self):
        return self.srepr()
    
    def __eq__(self, other):
        return hash(self) == hash(other)
        
    def __ne__(self, other):
        return not(self == other)
        
    def __neg__(self):
        return -1*self
    
    def __add__(self, other):

        if other == 0:
            return self
        
        if is_scalar(other) and is_scalar(self):
            return Plus(self, other)
        
        elif isinstance(self,Serie) or isinstance(other,Serie):        
            return PlusSeries(self,other)
            
        else:
            raise TypeError("unsupported operand type(s) for +: " +\
                                type(self).__name__ + ' and ' +\
                                    type(other).__name__)
    def __radd__(self, other):
        return  self + other 
    
    def __sub__(self, other):
        return self + -1*other
    
    def __rsub__(self, other):
        return -1*self + other
    
    def __pow__(self, other):
        if isinstance(self,Serie):
            return SeriePow(self,other)
        else:    
            return ScalPow(self, other)
    
    def __rpow__(self,other): 
        return other**self
    
    def __mul__(self, other):
        if is_scalar(self) and is_scalar(other):
            return Mult(self, other)
        
        elif isinstance(self,Serie) or isinstance(other,Serie) :
            return MultSeries(self,other)
        
        else:
            raise TypeError("unsupported operand type(s) for *: " +\
                                type(self).__name__ + ' and ' +\
                                    type(other).__name__)
            
    def __rmul__(self, other):
        return self * other
    
    def __truediv__(self, other):
        if is_scalar(self) and is_scalar(other):
            return Mult(ScalPow(other, -1), self)
        else:
            raise TypeError("unsupported operand type(s) for *: " +\
                                type(self).__name__ + ' and ' +\
                                    type(other).__name__)
            
    def __rtruediv__(self, other):
        if is_scalar(self) and is_scalar(other):
            return Mult(ScalPow(self, -1), other)
        else:
            raise TypeError("unsupported operand type(s) for *: " +\
                                type(self).__name__ + ' and ' +\
                                    type(other).__name__)
            
    
        

    
    
class Scalar(Expr):
    
    def __init__(self, name, value = None):
        if not isinstance(name, str):
            raise ValueError('Name of scalar must be a string.')
        self.name = name
        self.value = value
        self.scalar = True
        self.symbol = None
        self.args = (name,)
        self._mhash = None
        
    def getargs(self):
        return (self.name,)
    
    def __repr__(self):
        return self.name
        
    def latex(self):
        return self.name
    
            
    def srepr(self):
        return repr(self)
   
    def set_value(self, value):
        self.value = value
    
    def sympy(self):
        if self.symbol == None:
            self.make_symbol()
        return self.symbol
    
    def make_symbol(self):
        self.symbol = sp.symbols(self.name)
        symbol_dict[self.symbol] = self
        
    def clean_symbol(self):
        del symbol_dict[self.symbol]
        self.symbol = None
    
    
    def derived(self,coordinate):
        if self.name == coordinate.name:
            return 1
        else: 
            return 0
        


class ScalPow(Expr):

    def __new__(cls, *args):
        if not all(map(is_scalar, args)):
            raise TypeError('ScalPow should only involve Scalar objects.')
        instance = super(ScalPow, cls).__new__(cls)
        instance.args = args
        if len(instance.args) > 2:
            raise TypeError('ScalPow takes 2 arguments but ' + \
                            len(instance.args)  + ' were given.')
            
        elif len(instance.args) == 1:
            return instance.args[0]
        elif instance.args[0] == 1:
            return 1
        elif instance.args[1] == 0:
            return 1
        elif instance.args[1] == 1:
            return instance.args[0]
        elif all(map(is_number, args)):
            if instance.args[0] == 0 and instance.args[1] < 0 :
                raise ZeroDivisionError('Division by zero')
            else:
                return instance.args[0]**instance.args[1]
        else:
            return instance
        
    def __init__(self, *args):
        self._mhash = None
        self.scalar = True
        self.base = self.args[0]
        self.exp = self.args[1]
        
    def __repr__(self):
        """
        falta revisar cuando la base es mult y plus <--malo
        >> 2**(x*y)
        print --> 2^y*x 
        debe ser :2^(y*x) --> listo 
        falta implementar Scalars negativos: hacer mult
        
        """
        if is_number(self.base):
            base_string = str(self.base)
        else:
            base_string = repr(self.base)
            if isinstance(self.base, Mult) or isinstance(self.base, Plus) : 
                base_string = '(' + base_string + ')'
        
        if is_number(self.exp) and self.exp < 0:
            if self.exp == -1:
                return '(1/' + base_string + ')'
            exp_string = str(-self.exp)
            return '(1/(' + base_string + '^' + exp_string + '))'
        else:
            exp_string = repr(self.exp) 
            if isinstance(self.exp, Mult)  : 
                exp_string = '(' + exp_string + ')'
            return  base_string + '^' + exp_string
        
    def latex(self):
        if is_number(self.base):
            base_string = str(self.base)
        else:
            base_string = self.base.latex()
            if isinstance(self.base, Mult) or isinstance(self.base, Plus)   : 
                base_string = '(' + base_string + ')'
        
        if is_number(self.exp) and self.exp < 0   :
            exp_string = str(-self.exp)
            return '\\frac{1}{' + base_string + '^' + exp_string + '}'
        else:
            exp_string = repr(self.exp) if is_number(self.exp) else self.exp.latex()
            if len(exp_string) > 1:
                exp_string = '{' + exp_string +'}'
            return base_string + '^' + exp_string
    
    
    def sympy(self):
        return sp.Pow(sympy(self.base), sympy(self.exp))
    
    def expanded(self): 
        terms = self.base.args
        if isinstance(self.base,Mult):
            new_args=list(map(lambda term :term**self.exp,terms))
            return Mult(*new_args)
        elif isinstance(self.base,Plus) and isinstance(self.exp, int) : 
            all_args = self.exp * [terms]
            new_args = _distribute_terms(all_args)
            return Plus(*new_args)
        else: 
            return self 
        
    def derived(self,coordinate):
        if dependency(self.exp,coordinate) : 
            print("implementar log natural")
        if isinstance(self.base,Scalar):
            if dependency(self.base,coordinate): 
                new_expo = self.exp - 1
                term = self.exp*self.base**new_expo
                return term
            else: 
                return 0
        else: 
            return derived(self.expanded(),coordinate)
    

                

            

class Mult(Expr, Associative, Commutative, Identity, Cummulative, 
              NullElement):
    
    def __new__(cls, *args):
        if not all(map(is_scalar, args)):
            raise TypeError('ScalMul should only involve Scalar objects.')
        instance = super(Mult, cls).__new__(cls)
        instance._identity_ = 1
        instance._null_ = 0
        instance.args = args
        instance.make_associative()
        if instance.is_null():
            return 0
        instance.simplify(ScalPow, lambda a, b: a + b,
                          instance._separate_exp)
        instance.ignore_identity()
        instance.make_commutative()
        if len(instance.args) == 1:
            return instance.args[0]
        elif all([is_number(a) for a in instance.args]):
            return prod(instance.args)
        else:
            return instance
        
    def __init__(self, *args):
        self.scalar = True
        self._mhash = None
    

    def __repr__(self):
        s = [self._separate_exp(a) for a in self.args]
        numer = ''
        denom = ''

        for p, b in s:

            if isinstance(b,Plus): 
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
        
    def latex(self):
        s = [self._separate_exp(a) for a in self.args]
        numer = ''
        denom = ''
        for p, b in s:
            if isinstance(b,Plus): 
                b_str = '(' + repr(b) + ')' 
            elif b == -1 :
                b_str = "-" 
            else:
                b_str = str(b) if is_number(b) else b.latex()  

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
                    p_str = str(p) if is_number(p) else p.latex()
                    numer += ' ' + b_str + '^' + p_str

        if len(numer) == 0:
            numer = str(1)
        else:
            numer = numer[1:]
                
        if len(denom) == 0:
            return numer
        else:
            return '\\frac{' + numer + '}{' + denom + '}'
    
    def sympy(self):
        return sp.Mul(*[sympy(a) for a in self.args])
    
    def _number_version(self, *args):
        return prod(args)
    
    def _separate_exp(self, term):
        if isinstance(term, ScalPow) and is_number(term.args[1]):
            return term.args[1], term.args[0]
        else:
            return 1, term
    
    def expanded(self):
        terms = list(map(expand,self.args))
        plus_terms = [f.args for f in terms if isinstance(f,Plus)]
        rest_terms = [f for f in terms if not isinstance(f,Plus)]
        left = Mult(*rest_terms)
        if len(plus_terms)==0:
            return left
        expand_plus = _distribute_terms(plus_terms)
        rigth = Plus(*expand_plus)
        new_args = list(map(lambda f: left*f,expand_plus)) 
        return Plus(*new_args)
    
    def derived(self,coordinate): 
        if dependency(self,coordinate):
            new_terms=[]
            terms = [f for f in self.args]
            for i in range(len(terms)): 
                new_element = [e for e in terms]
                new_element[i] = derived(new_element[i],coordinate)
                new_terms.append(Mult(*new_element))
            return Plus(*new_terms)
        else: 
            return 0
        

            
        
class Plus(Expr, Associative, Commutative, Identity, Cummulative):
    
    def __new__(cls, *args):
        if not all(map(is_scalar, args)):
            raise TypeError('Plus should only involve Scalar objects.')
        instance = super(Plus, cls).__new__(cls)
        instance._identity_ = 0
        instance.args = args
        instance.make_associative()
        instance.ignore_identity()
        if len(instance.args)==0: 
            return 0
        instance.simplify(Mult, instance._number_version, 
                          instance._separate_num)
        instance.make_commutative()
        if len(instance.args) == 1:
            return instance.args[0]
        if all([is_number(a) for a in instance.args]):
            return sum(args)
        else:
            return instance
    
    def __init__(self, *args):
        self.scalar = True
        self._mhash = None 

    def _separate_num(self, term):
        if isinstance(term, Mult) and is_number(term.args[0]):
            return term.args[0], Mult(*term.args[1:])
        else:
            return 1, term
        
    def __repr__(self):
        l = [(str(a) if is_number(a) else repr(a)) for a in self.args]
        return ' + '.join(l)
        
    def latex(self):
        l = [(str(a) if is_number(a) else a.latex()) for a in self.args]
        return ' + '.join(l) 
    
    def sympy(self):
        return sp.Add(*[sympy(a) for a in self.args])
    
    def _number_version(self, *args):
        return sum(args)
    
    def expanded(self):
        terms = list(map(expand,self.args))
        return Plus(*terms)
    
    def derived(self,coordinate): 
        terms = self.expanded().args
        new_terms = list(map(lambda x:derived(x,coordinate),terms))
        return Plus(*new_terms)
    

    

    





class Deriv(Expr):
    def __new__(cls, base , coordinate = []):
        instance = super(Deriv, cls).__new__(cls)
        instance._mhash = None
        instance.base = base
        instance.coordinate = coordinate 
        if isinstance(instance.base,Deriv):
            intance.base = instance.base.base
            new_coo = instance.coordinate + instance.base.coordinate
            instance.coordinate = new_coo
        return instance     
                
    def __init__(self, base, coordinate = []):  
        self.args=(base,coordinate)
        
    def __repr__(self):
        return "∂(" + repr(self.base) +\
                            ',' +' '.join(repr(f) for f in self.coordinate)  + ')'
    
    def latex(self):
        return '\partial_{' + ' '.join(f.latex() for f in self.coordinate)+'}' +\
                                                    '(' + self.base.latex() +')'
    def expanded(self): 
        aux  =None
        base = self.base.expanded()
        for coo in self.coordinate:
            aux = derived(base,coo) if aux == None else derived(aux,coo)     
        return aux

    
    
    

    
def _sum_by_order(terms):
    aux=None
    by_order=[]
    plus = 0
    for term in terms: 
        if aux==None: 
            aux=term[0] 
            plus=term[1]
        elif aux==term[0]:
            plus += term[1]
        else:
            by_order.append((aux,plus))
            aux=term[0]
            plus = term[1]
    by_order.append((aux,plus))  
    return by_order

def dependency(exp,coordinate): 
    if is_number(exp): 
        return False 
    if isinstance(exp,Scalar):
        if exp == coordinate: 
            return True
        else: 
            return False 

    is_dependent = [f for f in exp.args if dependency(f,coordinate)]    
    if isinstance(exp,Mult) or isinstance(exp,Plus)\
                            or isinstance(exp,ScalPow):
        if len(is_dependent) != 0:
            return True 
        else:
            return False
        

def get_order_by_variable(expr,variable): 
    expr=expand(expr)
    if not dependency(expr,variable): 
        return [(0,expr)]
    else: 
        if isinstance(expr,Scalar): 
            return [(1,expr)]
        elif isinstance(expr,ScalPow): 
            return [(expr.exp,expr)]
        elif isinstance(expr,Mult):
            for i in range(len(expr.args)):
                if dependency(expr.args[i],variable): 
                    order = get_order_by_variable(expr.args[i],variable)[0][0]
                    return [(order,expr)]
        elif isinstance(expr,Plus): 
            terms=[get_order_by_variable(f,variable)[0] for f in expr.args]
            terms.sort(key=lambda tup: tup[0])
            by_order= _sum_by_order(terms)
            return by_order
    
def _variables(exp): 
    terms=[]
    if isinstance(exp,Scalar):
        return [exp]
    
    elif isinstance(exp,ScalPow):
        base = expand(exp.base)
        if isinstance(base,Scalar): 
            terms.append(base)
        else:
            var=[_variables(f)[0] for f in base.args if isinstance(_variables(f),list)  ] 
            terms.extend(var)
 
    elif isinstance(exp,Mult) or isinstance(exp,Plus) :
        var=[_variables(f)[0] for f in exp.args if isinstance(_variables(f),list) ] 
        terms.extend(var)
        
    termsf =list(filter(None.__ne__, terms))
    return termsf


class Serie(Expr):
    
    def __init__(self,args=[],coordinate=None, order = None, for_tensor = False ): 
        if coordinate == None:
            coo = self.search_dependency(args)
            if len(coo)>1:
                raise ValueError("For multivalued Series you must specify the expansion coordinate.") 
            self.coordinate = list(coo)[0]
        else:
            self.coordinate= coordinate 
        expr = Plus(*args) if not for_tensor else self#agregar cuando sera tensor 
        self.args = dict(get_order_by_variable(expr,self.coordinate))
        self.order = self.highest_order() + 1 if order == None  else order
        self._mhash = None
        
    def __repr__(self): 
        return  ' + '.join(repr(self.args[arg]) for arg in self.args) +\
                                            ' + O(ϵ^%s)'%(self.order)
    
    def search_dependency(self,args):
        variables=[ ]
        for arg in args :
            variables.extend(_variables(arg))
        return set(variables)
    

    def get_order(self,order): 
        try:
            return self.args[order]
        except KeyError :
            return 0
    
    def make_plus(self): 
        args = [self.args[arg] for arg in self.args]
        return Plus(*args)
    
    def derived(self):
        terms = self.base.args
        new_serie=[deriv(terms[f],self.coordinate) for f in terms]
        return Serie(*new_serie)   
    
    def highest_order(self): 
        return list(self.args.keys())[-1]
    


    

class SeriePow(Serie): 
    
    def __new__(cls, *args):
        if not (isinstance(args[0],Serie) and is_scalar(args[1])):
            raise TypeError('ScalSerie should only involve Series objects.')
        instance = super(SeriePow, cls).__new__(cls)
        instance.args = args
        if len(instance.args) > 2:
            raise TypeError('ScalPow takes 2 arguments but ' + \
                            len(instance.args)  + ' were given.')
            
        elif len(instance.args) == 1:
            return instance.args[0]
        elif instance.args[0] == 1:
            return 1
        elif instance.args[1] == 0:
            return 1
        elif instance.args[1] == 1:
            return instance.args[0]
        else:
            return instance
        
    def __init__(self, *args):
        self._mhash = None
        self.scalar = True
        self.base = self.args[0]
        self.exp = self.args[1]
        
    def __repr__(self):
        return repr((self.base.make_plus())**self.exp)
        
    def latex(self):
        return ((self.base.make_plus())**self.exp).latex()
    
    def sympy(self):
        return sp.Pow(sympy(self.base.make_plus()), sympy(self.exp))
    
    def expanded(self): 
        if isinstance(self.exp, int):
            all_args = self.exp * [self.base]
            return MultSeries(*all_args)
        else: 
            return self


    
    
class PlusSeries(Serie):
    
    """ 
    asumo que ambas series tienen la misma coordenada de expancion 
    """
    
    def __new__(cls,*args): 
        instance = super(PlusSeries, cls).__new__(cls)
        coordinate=args[0].coordinate
        instance.args = instance.distribute(args)
        return Serie(instance.args,coordinate)
        
    
    def distribute(self,args): 
        series = [f for f in args ]
        if not all(map(lambda x: isinstance(x,Serie),series)): 
            return self.simple_distribute(args)
        series.sort(key= lambda Serie: Serie.order)
        smallest = series[0]
        term_pos = [Plus(*(f.args[i] for f in args)) for i in smallest.args.keys()] 
        return term_pos
    
    def simple_distribute(self,args): 
        scalar = [f for f in args if not isinstance(f,Serie)][0]
        serie_args = [f for f in args if  isinstance(f,Serie)][0].args
        new_serie = [serie_args[i] if i!=0 else serie_args[i]+scalar for i in serie_args  ] 
        return new_serie

        
    def __str__(self): 
        return super().__repr__()


        
class MultSeries(Serie): 
    
    def __new__(cls,*args):  
        instance = super(MultSeries, cls).__new__(cls)
        coordinate =  [f for f in args if isinstance(f,Serie)][0].coordinate
        instance.args = instance.distribute(args)
        expr=Plus()
        return Serie(instance.args,coordinate)
    
    def __init__(self,*args): 
        self
        
    def distribute(self,args): 
        new_args = dict() 
        args = [f for f in args]
        if not all(map(lambda x: isinstance(x,Serie),args)): 
            return self.simple_distribute(args)
        series = sorted(args,key= lambda Serie: Serie.order)
        for i in series[1].args.keys(): 
            for j in series[0].args.keys():
                if i+j < series[0].order:
                    try: 
                        aux = new_args[j+i]
                        new_args[j+i] = series[0].args[j] * series[1].args[i] + aux
                    except KeyError: 
                        new_args[j+i] = series[0].args[j] * series[1].args[i]   
        new_args=[f for f in new_args.values()]
        return new_args
    
    def simple_distribute(self,args): 
        scalar = [f for f in args if not isinstance(f,Serie)][0]
        serie_args = [f for f in args if  isinstance(f,Serie)][0].args
        new_serie = [serie_args[i]*scalar for i in serie_args ] 
        return new_serie
    
    
    
    def __repr__(self): 
        return super().__repr__()
    
    
    


        