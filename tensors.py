from algebra import Expr 



def indexs(names):
    return tuple(Index(name[0],name[1]) for name in names)




class Index(Expr):
    """
        0 -> upper indices 
        1 -> lower index
        2 -> contracted index
    """

    def __new__(cls,name,position,coordinates=None):
        if not isinstance(name, str):
            raise TypeError('Name of index must be a string.')
        if not position in [0,1,2]:
            raise ValueError('Position invalid.')
        instance = super(Index, cls).__new__(cls)
        if position == 2: 
            return ContractedIndex(name,position,coordinates=None)
        instance.name = name
        instance.position = position 
        instance.coordinates = coordinates
        instance.args = (name,position,coordinates)
        return instance

    
    def __init__(self,name,position,coordinates=None):
        self._mhash= None
        self.is_index = True
        self.is_contracted = False
    
    def srepr(self):
        pos = self.position 
        name = self.name
        ind_str = f'{"_"}{name}' if pos==0 else f'{"^"}{name}'
        return ind_str
                 
    def __repr__(self):
        return self.srepr()
    
    def set_coordinates(self, coordinates):
        self.coordinates = coordinates
    

    
    

        

class ContractedIndex(Expr): 

    def __init__(self,name,position,coordinates=None):
        self.name = name
        self.position = position 
        self.coordinates = coordinates
        self.args = (name,position,coordinates)
        self._mhash= None
        self.is_index = True
        self.is_contracted = True
    
    def srepr(self):
        return f'{"Ç"}{self.name}'
                 
    def __repr__(self):
        return self.srepr()




