#GODEL NUMBERING SYSTEM IN PYTHON

#credit:
"""
Credit to this guy: https://github.com/jackolantern
Took it from here: https://github.com/jackolantern/godel
"""

#usage:
"""
Godel = GodelNumbering()
print(Godel.encode("0=0")) - returns 270,000,000
print(Godel.decode(270000000)) - returns 0=0
"""

#function:
def GodelNumbering():
    from re import Scanner
    from itertools import groupby, takewhile
    from math import sqrt
    def sieve(n):
      if n < 2: return []  
      lng = int((n / 2) - 1 + n % 2)  ## Remove even numbers.
      sieve = [True] * (lng + 1)  
      for i in range(int(sqrt(n)) >> 1):  
        if not sieve[i]: continue
        for j in range( (i * (i + 3) << 1) + 3, lng, (i << 1) + 3):  
          sieve[j] = False
      primes = [2] + [(i << 1) + 3 for i in range(lng) if sieve[i]]
      return primes
    def factor(n):
      factor = 2
      factors = []
      while factor <= n:
        if n % factor == 0:
          n //= factor
          factors.append(factor)
        else:
          factor += 1
      return factors
    import collections
    class Bijection:
      def __init__(self, mapping):
        inverse = {}
        for k, v in mapping.items():
          if v in inverse:
            raise ValueError("duplicate key '{0}' found".format(v))
          inverse[v] = k
        self._mapping = dict(mapping)
        self._inverse = inverse
      def __len__(self):
        return len(self.mapping)
      @property
      def mapping(self):
        return self._mapping
      @property
      def inverse(self):
        return self._inverse
    def prod(iterable):
      product = 1
      for n in iterable:
        product *= n
      return product
    UPPERBOUND_OF_PRIMES = 10000
    TICK = '`'
    NUMERICAL_VARIABLES = 'x', 'y', 'z'
    SENTNTIAL_VARIABLES = 'p', 'q', 'r'
    PREDICATE_VARIABLES = 'P', 'Q', 'R'
    ALL_VARIABLES = NUMERICAL_VARIABLES + SENTNTIAL_VARIABLES + PREDICATE_VARIABLES
    CONSTANT_SIGNS = Bijection({
      '~' : 1,
      '∨' : 2,
      '⊃' : 3,
      '∃' : 4,
      '=' : 5,
      '0' : 6,
      's' : 7,
      '(' : 8,
      ')' : 9,
      ',' : 10,
      '+' : 11,
      '×' : 12
    })
    PRIME = sieve(UPPERBOUND_OF_PRIMES)
    MAX = max(CONSTANT_SIGNS.mapping.values())
    PRIME_OFFSET = len(list(takewhile(lambda x: x < MAX, PRIME)))
    class LexicalException(Exception):
      def __init__(self, value):
        self.value = value
      def __str__(self):
        return repr(self.value)
    class Lexer:
      constant_type = "C"
      numerical_type = "N"
      sentntial_type = "S"
      predicate_type = "P"
      def __init__(self):
        self.constant_signs = self.match_any(CONSTANT_SIGNS.mapping.keys())
        self.numerical_variables = self.match_any_with_ticks(NUMERICAL_VARIABLES)
        self.sentntial_variables = self.match_any_with_ticks(SENTNTIAL_VARIABLES)
        self.predicate_variables = self.match_any_with_ticks(PREDICATE_VARIABLES)
      def match_any(self, iterable):
        """
        Returns a regex which matches any character in "iterable."
        """
        return "[%s]" % ''.join(iterable)
      def match_any_with_ticks(self, iterable):
        return "{0}{1}*".format(self.match_any(iterable), TICK)
      def scan(self, string):
        scanner = Scanner([
          (self.constant_signs, lambda _, tok: (self.constant_type, tok)),
          (self.numerical_variables, lambda _, tok: (self.numerical_type, tok)),
          (self.sentntial_variables, lambda _, tok: (self.sentntial_type, tok)),
          (self.predicate_variables, lambda _, tok: (self.predicate_type, tok))])
        tokens, remainder = scanner.scan(string)
        if remainder:
          if len(remainder) > 10:
            remainder = remainder[:10]
          raise LexicalException("Error lexing input near {0}...".format(remainder))
        return tokens
    class State:
      def __init__(self):
        self.encoding = []
        self.numerical_variables = {}
        self.sentntial_variables = {}
        self.predicate_variables = {}
      def next_var_name(self, assigned, pool):
        poollen = len(pool)
        count = len(assigned)
        ticks = count // poollen
        name = pool[count % poollen] + TICK * ticks
        return name
      def encode_constant_sign(self, symbol):
        return CONSTANT_SIGNS.mapping.get(symbol)
      def encode_numerical_variable(self, symbol):
        gnum = self.numerical_variables.get(symbol)
        if gnum:
          return gnum
        else:
          gnum = PRIME[PRIME_OFFSET + len(self.numerical_variables)]
          self.numerical_variables[symbol] = gnum
          return gnum
      def encode_sentntial_variable(self, symbol):
        gnum = self.sentntial_variables.get(symbol)
        if gnum:
          return gnum
        else:
          gnum = PRIME[PRIME_OFFSET + len(self.sentntial_variables)]**2
          self.sentntial_variables[symbol] = gnum
          return gnum
      def encode_predicate_variable(self, symbol):
        gnum = self.sentntial_variables.get(symbol)
        if gnum:
          return gnum
        else:
          gnum = PRIME[PRIME_OFFSET + len(self.sentntial_variables)]**3
          self.sentntial_variables[symbol] = gnum
          return gnum
      def decode_numerical_variable(self, gnum):
        symbol = self.numerical_variables.get(gnum)
        if symbol:
          return symbol
        symbol = self.next_var_name(self.numerical_variables, NUMERICAL_VARIABLES)
        self.numerical_variables[gnum] = symbol
        return symbol
      def decode_sentential_variable(self, gnum):
        symbol = self.sentntial_variables.get(gnum)
        if symbol:
          return symbol
        symbol = self.next_var_name(self.sentntial_variables, SENTNTIAL_VARIABLES)
        self.sentntial_variables[gnum] = symbol
        return symbol
      def decode_predicate_variable(self, gnum):
        symbol = self.predicate_variables.get(gnum)
        if symbol:
          return symbol
        symbol = self.next_var_name(self.predicate_variables, PREDICATE_VARIABLES)
        self.predicate_variables[gnum] = symbol
        return symbol  
    def encode(string):
      if not string: return 0
      state = State()
      lexer = Lexer()
      tokens = lexer.scan(string)
      lexmap = {
        lexer.constant_type  : state.encode_constant_sign,
        lexer.numerical_type : state.encode_numerical_variable,
        lexer.sentntial_type : state.encode_sentntial_variable,
        lexer.predicate_type : state.encode_predicate_variable
      }
      for token_type, lexeme in tokens:
        lookup = lexmap[token_type]
        gnum = lookup(lexeme)
        state.encoding.append(gnum)
      retval = prod(PRIME[idx]**gnum for idx, gnum in enumerate(state.encoding))
      return retval
    def decode(number):
      if not number: return ""
      state = State()
      symbols = []
      factors = ((k, len(list(v))) for k, v in groupby(factor(number)))
      for i, (f, gnum) in enumerate(factors):
        if PRIME[i] != f:
          err = "not a Gödel number: prime at index {0} is {1} but should be {2}."
          err = err.format(i, f, PRIME[i])
          raise ValueError(err)
        symbol = CONSTANT_SIGNS.inverse.get(gnum)
        if not symbol:
          if gnum in PRIME:
            symbol = state.decode_numerical_variable(gnum)
          else:
            factors = factor(gnum)
            if len(set(factors)) != 1:
              err = '{0} is not prime, a prime squared, or a prime cubed.'
              err = err.format(gnum)
              raise ValueError(err)
            if len(factors) == 2 and factors[0] in PRIME:
              symbol = state.decode_sentential_variable(gnum)
            elif len(factors) == 3 and factors[0] in PRIME:
              symbol = state.decode_predicate_variable(gnum)
            else:
              err = '{0} is not prime, a prime squared, or a prime cubed.'
              err = err.format(gnum)
              raise ValueError(err)
        symbols.append(symbol)
      return ''.join(symbols)
    r_obj = lambda:None
    setattr(r_obj,"encode",encode)
    setattr(r_obj,"decode",decode)
    return r_obj
