r"""
Super Multiset RSK
"""
#*****************************************************************************
#       Copyright (C) 2023 Alexander Wilson <niesswilson@gmail.com>,
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************
r"""
    REFERENCES:

    .. [W23] A. Wilson, Super multiset RSK and a mixed multiset partition
    algebra, :arXiv:`2308.07238`
"""

import functools
from sage.rings.integer import Integer

@functools.total_ordering
class SuperValue ():
    def __init__ (self, value):
        r"""
        Initialize ``self``

        INPUT:

        - ``value`` -- an integer where negative values correspond to barred elements

        EXAMPLES::

            sage: l = SuperValue(-3)
        """
        if type(value) is SuperValue:
            self._value = value._value;
        else:
            self._value = value;
    def __eq__ (self, other):
        return self._value == other._value;
    
    def parity (self):
        r"""
            Return the parity of the value (0 if unbarred, 1 if barred)
        """
        if self._value > 0:
            return 0;
        else:
            return 1;
    
    # All "barred" numbers (stored as negatives) are larger than all unbarred numbers
    def __lt__ (self, other):
        if self._value < 0:
            if other._value < 0:
                # Compare as negatives
                return self._value > other._value;
            else:
                # self is barred, other is not
                return False;
        else:
            if other._value < 0:
                # self is unbarred, other is barred
                return True;
            else:
                # Compare as positives
                return self._value < other._value;

    def __repr__ (self):
        return str(self._value);

# Gets the parity of a value
def _parity (x):
    if type(x) is SuperValue:
        return x.parity();
    if type(x) is Integer or type(x) is int:
        if x < 0:
            return 1;
        else:
            return 0;
    
@functools.total_ordering
class SuperMultiSet:
    def __init__ (self, array):
        r"""
        Initialize ``self``

        INPUT:

        - ``array`` -- a list of integers comprising the multiset

        EXAMPLES::

            sage: S = SuperMultiSet([1,1,-2])
        """
        if type(array) is SuperMultiSet:
            self._unbarred = array._unbarred[0:];
            self._barred = array._barred[0:];
        else:
            self._unbarred = sorted([SuperValue(x) for x in array if _parity(x) == 0]);
            self._barred = sorted([SuperValue(x) for x in array if _parity(x) == 1]);
    def __eq__ (self, other):
        if type(other) is not SuperMultiSet:
            return False;
        return self._unbarred == other._unbarred and self._barred == other._barred;
    
    # i is the index at which we start comparing (i.e. take out the i largest elements)
    def __lt__ (self, other, i = 0):
        if len(self) - i == 0 and len(other) - i == 0:
            return False;
        
        if len(self) - i == 0 and len(other) - i > 0:
            return True;
        
        if len(self) - i > 0 and len(other) - i == 0:
            return False;
        
        if i > 0:
            smax = max(list(self)[0:-i]);
            omax = max(list(other)[0:-i]);
        else:
            smax = max(self);
            omax = max(other);
        
        if smax < omax:
            return True;
        
        if smax > omax:
            return False;
        
        if smax == omax:
            return self.__lt__(other, i + 1);
    
    def parity (self):
        r"""
            Return the parity of the multiset (0 if it contains an even number of
            barred elements, 1 if it contains an odd number)
        """
        return len(self._barred) % 2;
    
    def __len__ (self):
        return len(self._unbarred) + len(self._barred);
    
    def __repr__ (self):
        return "[" + ", ".join([str(x) for x in self._unbarred + self._barred]) + "]";
    
    def __iter__ (self):
        for x in self._unbarred:
            yield x;
        for y in self._barred:
            yield(y);
    
            
# TODO: could extend a more general super tableau class that only asks that its entries be
# totally ordered and have a .parity() method
class SuperMultiSetPartitionTableau:
    def __init__ (self, tableau):
        r"""
        Initialize ``self``

        INPUT:

        - ``tableau`` -- a list of lists, each filled with multisets representing a row of the tableau

        EXAMPLES::

            sage: S = SuperMultiSetPartitionTableau([[[1],[1]],[[1,1,-2]]])
        """
        self._tableau = [];
        
        for row in tableau:
            _row = [SuperMultiSet(A) for A in row];
            self._tableau.append(_row);

    # TODO: more sophisticated printing...
    def __repr__ (self):
        out = [];
        for i in range(0, len(self._tableau)):
            row = self._tableau[len(self._tableau) - i - 1];
            out.append(" ".join([str(A) for A in row]));
        
        return "\n".join(out);
    
    def __len__ (self):
        return len(self._tableau);
    
    def __iter__ (self):
        for row in self._tableau:
            yield row;
    
    def __getitem__ (self, y):
        return self._tableau[y];
    
    # Perform (parity)-insertion of the value A into the tableau T
    # in (row/column) index
    # returns the coordinates of the final insertion
    def insert(self, A, parity = 0, index = 0):
        r"""
        Perform (parity)-insertion of the value A into the tableau T

        INPUT:

        - ``A`` -- the value to be inserted

        - ``parity`` -- 0 or 1, indicating the kind of insertion to perform (defaults to 0)

        - ``index`` -- the index of the row or column to insert into (defaults to the first)

        EXAMPLES::

            sage: T = SuperMultiSetPartitionTableau([[[1],[1]],[[1,1,-2]]])
            sage: T.insert([1,1], 1)
        """
        if not type(A) is SuperMultiSet:
            A = SuperMultiSet(A);
        
        # Handling an empty tableau;
        if len(self) == 0:
            self._tableau.append([A]);
            return [0,0];
        
        # Row insertion
        if parity == A.parity():
            y = index;
            
            # If we're inserting to an empty row,
            if y == len(self):
                self._tableau.append([A]);
                return [0, y];
            
            row = self[y];

            for x in range(0, len(row)):
                B = row[x];
                # 0-insertion checks for strictly greater than
                # 1-insertion checks for weakly greater than
                if (parity == 0 and B > A) or (parity == 1 and B >= A):
                    # Bump B
                    self._tableau[y][x] = A;
                    if B.parity() == parity:
                        # new index is the next row
                        new_index = y + 1;
                    else:
                        # new index is the next column
                        new_index = x + 1;
                    return self.insert(B, parity, new_index);
            
            # If greater than or equal to everything in the row, 
            # just put it on the end
            
            row.append(A);
            
            return [len(row) - 1, y];
        # Column insertion
        else:
            x = index;
            
            # If inserting into an empty column,
            if x == len(self[0]):
                self[0].append(A);
                return [len(self[0]) - 1, 0];
            
            col = [row[x] for row in self if x < len(row)];
            
            for y in range(0, len(col)):
                B = col[y];
                # 0-insertion checks for strictly greater than
                # 1-insertion checks for weakly greater than
                if (parity == 0 and B > A) or (parity == 1 and B >= A):
                    # Bump B;
                    self._tableau[y][x] = A;
                    if B.parity() == parity:
                        # new index is the next row
                        new_index = y + 1;
                    else:
                        # new_index is the next column
                        new_index = x + 1;
                    return self.insert(B, parity, new_index);
            
            # If greater than or equal to everything in the column,
            # just put it at the end
            y = len(col);
            
            if y < len(self._tableau):
                self._tableau[y].append(A);
            else:
                self._tableau.append([A]);
            
            return [x,y];
        
    def extract (self, x, y, parity = 0, value = None):
        r"""
        Perform (parity)-extraction of a box out of the tableau T

        INPUT:

        - ``x``, ``y`` -- the coordinates of the value to extract

        - ``parity`` -- 0 or 1, indicating the kind of extraction to perform (defaults to 0)

        EXAMPLES::

            sage: T = SuperMultiSetPartitionTableau([[[1],[1]],[[1,1,-2]]])
            sage: T.extract(0, 0)
        """
        # First replace the value
        A = self._tableau[y][x];
        
        if value == None:
            if len(self._tableau[y]) != x + 1 or (len(self._tableau) > y + 1 and len(self._tableau[y + 1]) >= len(self._tableau[y])):
                raise TypeError("(" + str(x) + "," + str(y) + ") is not a removable corner of the tableau.");
            self._tableau[y] = self._tableau[y][0:-1];
            if len(self._tableau[y]) == 0:
                self._tableau = self._tableau[0:-1]
        else:
            self._tableau[y][x] = value;
        
        # If it would have been row-inserted in the first row or column-inserted in the first column,
        # we're done
        if (parity == A.parity() and y == 0) or (parity != A.parity() and x == 0):
            return A
                
        # If A was row-inserted
        if (parity == A.parity()):
            # we know A was bumped from the row below
            y0 = y - 1;
            row = self._tableau[y0];
            
            # Want the largest entry in row y0 which is (>/>=) A to bump
            for i in range(0, len(row)):
                x0 = len(row) - i - 1;
                if (parity == 0 and row[x0] < A) or (parity == 1 and row[x0] <= A):
                    return self.extract(x0,y0,parity,A);
        # If A as column-inserted
        else:
            # we know A was bumped from the column to the left
            x0 = x - 1;
            col = [row[x0] for row in self if x0 < len(row)];
            
            # Want the largest entry in col x0 which is (>/>=) A to bump
            for i in range(0, len(col)):
                y0 = len(col) - i - 1;
                if (parity == 0 and col[y0] < A) or (parity == 1 and col[y0] <= A):
                    return self.extract(x0,y0,parity,A);

SMPT = SuperMultiSetPartitionTableau;

@functools.total_ordering
class SuperBiLetter:
    def __init__ (self, array):
        r"""
        Initialize ``self``

        INPUT:

        - ``array`` -- a pair of values comprising the letter

        EXAMPLES::

            sage: w = SuperBiLetter([[2],[-1, -2]])
        """
        self._array = [SuperMultiSet(array[0]), SuperMultiSet(array[1])];
    def __eq__ (self, other):
        return self._array == other._array;
    
    def __lt__ (self, other):
        a1 = self._array[0];
        b1 = self._array[1];
        a2 = other._array[0];
        b2 = other._array[1];

        if a1 < a2:
            return True;

        if a1 != a2:
            return False;

        if b1.parity() != b2.parity():
            return b1.parity() == 1 and b2.parity() == 0;

        if b1.parity() == 0 and b2.parity() == 0:
            return b1 < b2;

        if b1.parity() == 1 and b2.parity() == 1:
            return b1 > b2;

    def __getitem__ (self, i):
        return self._array[i];

    def __repr__ (self):
        return str(self._array);


class SuperBiWord:
    def __init__ (self, array):
        r"""
        Initialize ``self``

        INPUT:

        - ``array`` -- a list of biletters

        EXAMPLES::

            sage: W = SuperBiWord([SuperBiLetter([[1,2],[2]]),SuperBiLetter([[-1],[-1]]),SuperBiLetter([[-1],[1,2]]),SuperBiLetter([[2],[-1,-2]])])
        """
        self._array = [SuperBiLetter(w) for w in array];

    def is_ordered (self):
        r"""
        Returns True iff the biword is ordered
        """
        return sorted(self._array) == self._array;

    def is_restricted (self):
        r"""
        Returns True iff the biword is restricted
        """

        for w in self._array:
            if self._array.count(w) > 1 and (w[0].parity() + w[1].parity()) == 1:
                return False;

        return True;

    def ordered (self):
        r"""
        Returns an ordered biword with the same letters as ``self``
        """
        return SuperBiWord(sorted(self._array));
    
    def __iter__ (self):
        for w in self._array:
            yield w;

    def __repr__ (self):
        top = [str(w[0]) for w in self._array];
        bot = [str(w[1]) for w in self._array];

        for i in range(0, len(top)):
            tl = len(top[i]);
            bl = len(bot[i]);

            if tl > bl:
                bot[i] = bot[i] + " " * (tl - bl);

            if bl > tl:
                top[i] = top[i] + " " * (bl - tl);

        return "  ".join(top) + "\n" + "  ".join(bot);

def sRSK (biword):
    r"""
        Perform super RSK on a given biword

        INPUT:

        - ``biword`` -- the ordered, restricted biword to be inserted

        EXAMPLES::

            sage: [P, Q] = sRSK([[[2],[-1,-2]],[[1,2],[2]],[[-1],[-1]],[[-1],[1,2]]])
        """

    biword = SuperBiWord(biword);

    if not biword.is_ordered() or not biword.is_restricted():
        raise TypeError("Super RSK can only be performed on an ordered, restricted biword");

    P = SMPT([]);
    Q = SMPT([]);
    
    for w in biword:
        [x,y] = P.insert(SuperMultiSet(w[1]), SuperMultiSet(w[0]).parity());
        if y < len(Q):
            Q[y].append(SuperMultiSet(w[0]));
        else:
            Q._tableau.append([SuperMultiSet(w[0])]);
    
    return [P, Q];

def _sRSK_inverse (P, Q):
    # copy
    P = SMPT(P._tableau)
    Q = SMPT(Q._tableau)

    if len(P) == 0:
        return [];
    # Find coordinate of largest value in Q
    # # In the case of a tie, look at the (right-most/top-most) node
    q = max([max(row) for row in Q]);

    # Read from top-to-bottom, then right-to-left within each row to
    # find first instance of the maximum
    for i in range(0, len(Q)):
        y = len(Q) - i - 1;
        row = Q[y];
        for j in range(0, len(row)):
            x = len(row) - j - 1;
            if row[x] == q:
                # Extract the corresponding value from p
                p = P.extract(x,y,q.parity());

                # Remove this node from Q
                if len(row) == 1:
                    Q._tableau = Q._tableau[0:-1];
                else:
                    Q._tableau[y] = row[0:-1];

                return _sRSK_inverse(P, Q) + [[q,p]];

def sRSK_inverse (P, Q):
    r"""
        Perform inverse super RSK on a pair of tableaux

        INPUT:

        - ``P`` -- the insertion tableau
        - ``Q`` -- the recording tableau

        EXAMPLES::

            sage: P = SMPT([[[1],[1],[2]],[[-1]],[[-2]]])
            sage: Q = SMPT([[[1],[1],[1]],[[2]],[[3]]])
            sage: sRSK_inverse(P, Q)
        """
    return SuperBiWord(_sRSK_inverse(P, Q));