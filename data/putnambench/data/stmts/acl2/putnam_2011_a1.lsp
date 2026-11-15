;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_a1:
;; exactly 10053 integer points in the square from (0,0) through (2011,2011)
;; cannot be endpoints of growing axis-aligned spirals. This file contains no
;; proof.

(in-package "ACL2")

;; A point is represented by the two-element list (x y), and a spiral by a
;; true list of such points. This is a bijective encoding of the source lists
;; of integer-coordinate pairs. The three lambdas traversing a witness use
;; only tame ACL2 primitives and standard APPLY$ scions.

;; The source existential quantifier remains internal. Every source spiral and
;; its positive strictly increasing length sequence form one two-element ACL2
;; witness, and every accepted witness decodes to such a source spiral.
;; Negated FN-EQUAL says that the failure predicate is false for some witness.

(defun putnam-2011-a1-quoted (object)
  (list 'quote object))

(defun putnam-2011-a1-list-term (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (putnam-2011-a1-list-term (cdr terms)))
    (putnam-2011-a1-quoted nil)))

(defun putnam-2011-a1-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (putnam-2011-a1-and-terms (cdr terms))
       (putnam-2011-a1-quoted nil))
    (putnam-2011-a1-quoted t)))

(defun putnam-2011-a1-not-term (term)
  (list
   'if
   term
   (putnam-2011-a1-quoted nil)
   (putnam-2011-a1-quoted t)))

(defun putnam-2011-a1-add-term (left right)
  (list 'binary-+ left right))

(defun putnam-2011-a1-nth-term (index values)
  (list 'nth index values))

(defun putnam-2011-a1-range-term (upper)
  (list
   'from-to-by
   (putnam-2011-a1-quoted 0)
   upper
   (putnam-2011-a1-quoted 1)))

(defun putnam-2011-a1-iteration-term (values)
  (list
   'loop$-as
   (putnam-2011-a1-list-term
    (list values))))

(defun putnam-2011-a1-point-entry-function ()
  (let* ((index (list 'car 'row))
         (spiral (list 'car 'globals))
         (point
          (putnam-2011-a1-nth-term index spiral)))
    (list
     'lambda
     '(globals row)
     (putnam-2011-a1-and-terms
      (list
       (list 'true-listp point)
       (list
        'equal
        (list 'len point)
        (putnam-2011-a1-quoted 2))
       (list
        'integerp
        (putnam-2011-a1-nth-term
         (putnam-2011-a1-quoted 0)
         point))
       (list
        'integerp
        (putnam-2011-a1-nth-term
         (putnam-2011-a1-quoted 1)
         point)))))))

(defun putnam-2011-a1-length-entry-function ()
  (let* ((index (list 'car 'row))
         (lengths
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 1)
           'globals))
         (current
          (putnam-2011-a1-nth-term index lengths))
         (previous
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-add-term
            index
            (putnam-2011-a1-quoted -1))
           lengths)))
    (list
     'lambda
     '(globals row)
     (putnam-2011-a1-and-terms
      (list
       (list 'posp current)
       (list
        'if
        (list
         'equal
         index
         (putnam-2011-a1-quoted 0))
        (putnam-2011-a1-quoted t)
        (list '< previous current)))))))

(defun putnam-2011-a1-segment-entry-function ()
  (let* ((index (list 'car 'row))
         (spiral (list 'car 'globals))
         (lengths
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 1)
           'globals))
         (current
          (putnam-2011-a1-nth-term index spiral))
         (next
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-add-term
            index
            (putnam-2011-a1-quoted 1))
           spiral))
         (length
          (putnam-2011-a1-nth-term index lengths))
         (current-x
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 0)
           current))
         (current-y
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 1)
           current))
         (next-x
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 0)
           next))
         (next-y
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 1)
           next))
         (direction
          (list
           'mod
           index
           (putnam-2011-a1-quoted 4)))
         (east
          (putnam-2011-a1-and-terms
           (list
            (list
             'equal
             (putnam-2011-a1-add-term
              current-x length)
             next-x)
            (list 'equal current-y next-y))))
         (north
          (putnam-2011-a1-and-terms
           (list
            (list 'equal current-x next-x)
            (list
             'equal
             (putnam-2011-a1-add-term
              current-y length)
             next-y))))
         (west
          (putnam-2011-a1-and-terms
           (list
            (list
             'equal
             (putnam-2011-a1-add-term
              current-x
              (list 'unary-- length))
             next-x)
            (list 'equal current-y next-y))))
         (south
          (putnam-2011-a1-and-terms
           (list
            (list 'equal current-x next-x)
            (list
             'equal
             (putnam-2011-a1-add-term
              current-y
              (list 'unary-- length))
             next-y)))))
    (list
     'lambda
     '(globals row)
     (list
      'if
      (list
       'equal
       direction
       (putnam-2011-a1-quoted 0))
      east
      (list
       'if
       (list
        'equal
        direction
        (putnam-2011-a1-quoted 1))
       north
       (list
        'if
        (list
         'equal
         direction
         (putnam-2011-a1-quoted 2))
        west
        south))))))

(defun putnam-2011-a1-all-indices-term
    (entry-function globals upper)
  (list
   'always$+
   (putnam-2011-a1-quoted entry-function)
   globals
   (putnam-2011-a1-iteration-term
    (putnam-2011-a1-range-term upper))))

(defun putnam-2011-a1-true-function ()
  (list
   'lambda
   '(witness)
   (putnam-2011-a1-quoted t)))

(defun putnam-2011-a1-witness-failure-function (x y)
  (let* ((witness 'witness)
         (spiral
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 0)
           witness))
         (lengths
          (putnam-2011-a1-nth-term
           (putnam-2011-a1-quoted 1)
           witness))
         (spiral-upper
          (putnam-2011-a1-add-term
           (list 'len spiral)
           (putnam-2011-a1-quoted -1)))
         (lengths-upper
          (putnam-2011-a1-add-term
           (list 'len lengths)
           (putnam-2011-a1-quoted -1)))
         (globals
          (putnam-2011-a1-list-term
           (list spiral lengths)))
         (qualification
          (putnam-2011-a1-and-terms
           (list
            (list 'true-listp witness)
            (list
             'equal
             (list 'len witness)
             (putnam-2011-a1-quoted 2))
            (list 'true-listp spiral)
            (list 'true-listp lengths)
            (putnam-2011-a1-not-term
             (list
              '<
              (list 'len spiral)
              (putnam-2011-a1-quoted 3)))
            (list
             'equal
             (list 'len lengths)
             spiral-upper)
            (list
             'equal
             (list 'car spiral)
             (putnam-2011-a1-quoted '(0 0)))
            (putnam-2011-a1-all-indices-term
             (putnam-2011-a1-point-entry-function)
             globals
             spiral-upper)
            (putnam-2011-a1-all-indices-term
             (putnam-2011-a1-length-entry-function)
             globals
             lengths-upper)
            (putnam-2011-a1-all-indices-term
             (putnam-2011-a1-segment-entry-function)
             globals
             lengths-upper)
            (list
             'equal
             (putnam-2011-a1-nth-term
              spiral-upper
              spiral)
             (putnam-2011-a1-quoted
              (list x y)))))))
    (list
     'lambda
     '(witness)
     (list
      'if
      qualification
      (putnam-2011-a1-quoted nil)
      (putnam-2011-a1-quoted t)))))

(defun putnam-2011-a1-reachable-p (x y)
  (let ((point-entry-function
         (putnam-2011-a1-point-entry-function))
        (length-entry-function
         (putnam-2011-a1-length-entry-function))
        (segment-entry-function
         (putnam-2011-a1-segment-entry-function))
        (failure-function
         (putnam-2011-a1-witness-failure-function x y))
        (true-function
         (putnam-2011-a1-true-function)))
    (and
     (tamep-functionp point-entry-function)
     (tamep-functionp length-entry-function)
     (tamep-functionp segment-entry-function)
     (tamep-functionp failure-function)
     (tamep-functionp true-function)
     (not (fn-equal failure-function true-function)))))

(defun putnam-2011-a1-unreachable-in-column-count
    (x y-count)
  (declare (xargs :measure (nfix y-count)))
  (if (zp y-count)
      0
    (let ((y (- y-count 1)))
      (+
       (if (putnam-2011-a1-reachable-p x y)
           0
         1)
       (putnam-2011-a1-unreachable-in-column-count
        x y)))))

(defun putnam-2011-a1-unreachable-square-count
    (x-count side-count)
  (declare (xargs :measure (nfix x-count)))
  (if (zp x-count)
      0
    (let ((x (- x-count 1)))
      (+
       (putnam-2011-a1-unreachable-in-column-count
        x side-count)
       (putnam-2011-a1-unreachable-square-count
        x side-count)))))

(defun putnambench-putnam-2011-a1-statement ()
  (equal
   (putnam-2011-a1-unreachable-square-count 2012 2012)
   10053))

(value-triple :itpeval-statement-checked)
:q
