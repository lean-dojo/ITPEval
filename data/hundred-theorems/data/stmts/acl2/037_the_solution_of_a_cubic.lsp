;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__037, "The Solution of a Cubic": Cardano data over
;; an arbitrary field with nonzero 2 and 3 and a primitive cube root of unity
;; characterize all three roots of a nondegenerate cubic, in the zero and
;; nonzero cases of its normalized depressed linear coefficient. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame APPLY$ function objects present the carrier and field operations.
;; FN-EQUAL with a constant-true function gives unbounded universal
;; quantification over the ACL2 universe, with the carrier predicate restricting
;; the field laws to the represented field. Thus the carrier may be infinite
;; and the operations are genuine functions rather than finite tables.

(defun ht037-quoted (object)
  (list 'quote object))

(defun ht037-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (ht037-term-list (cdr terms)))
    (ht037-quoted nil)))

(defun ht037-static-apply-term (function arguments)
  (list 'apply$
        (ht037-quoted function)
        (ht037-term-list arguments)))

(defun ht037-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (ht037-and-terms (cdr terms))
            (ht037-quoted nil))
    (ht037-quoted t)))

(defun ht037-not-term (term)
  (list 'if term
        (ht037-quoted nil)
        (ht037-quoted t)))

(defun ht037-implies-term (hypothesis conclusion)
  (list 'if hypothesis conclusion (ht037-quoted t)))

(defun ht037-true-function (formals)
  (list 'lambda formals (ht037-quoted t)))

(defun ht037-universal-p (function formals)
  (let ((always-true (ht037-true-function formals)))
    (and (tamep-functionp function)
         (tamep-functionp always-true)
         (fn-equal function always-true))))

(defun ht037-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun ht037-value1 (function x)
  (apply$ function (list x)))

(defun ht037-value2 (function x y)
  (apply$ function (list x y)))

;; An arbitrary nontrivial commutative field.

(defun ht037-field-laws-function
    (carrier zero one add multiply negate inverse)
  (let* ((xy-add (ht037-static-apply-term add '(x y)))
         (yz-add (ht037-static-apply-term add '(y z)))
         (xy-mul (ht037-static-apply-term multiply '(x y)))
         (yz-mul (ht037-static-apply-term multiply '(y z)))
         (neg-x (ht037-static-apply-term negate '(x)))
         (inv-x (ht037-static-apply-term inverse '(x))))
    (list
     'lambda '(x y z)
     (ht037-implies-term
      (ht037-and-terms
       (list (ht037-static-apply-term carrier '(x))
             (ht037-static-apply-term carrier '(y))
             (ht037-static-apply-term carrier '(z))))
      (ht037-and-terms
       (list
        (ht037-static-apply-term carrier (list xy-add))
        (ht037-static-apply-term carrier (list xy-mul))
        (ht037-static-apply-term carrier (list neg-x))
        (ht037-static-apply-term carrier (list inv-x))
        (list 'equal
              (ht037-static-apply-term add (list xy-add 'z))
              (ht037-static-apply-term add (list 'x yz-add)))
        (list 'equal xy-add
              (ht037-static-apply-term add '(y x)))
        (list 'equal
              (ht037-static-apply-term
               add (list 'x (ht037-quoted zero)))
              'x)
        (list 'equal
              (ht037-static-apply-term add (list 'x neg-x))
              (ht037-quoted zero))
        (list 'equal
              (ht037-static-apply-term multiply (list xy-mul 'z))
              (ht037-static-apply-term multiply (list 'x yz-mul)))
        (list 'equal xy-mul
              (ht037-static-apply-term multiply '(y x)))
        (list 'equal
              (ht037-static-apply-term
               multiply (list 'x (ht037-quoted one)))
              'x)
        (list 'equal
              (ht037-static-apply-term multiply (list 'x yz-add))
              (ht037-static-apply-term
               add
               (list
                (ht037-static-apply-term multiply '(x y))
                (ht037-static-apply-term multiply '(x z)))))
        (ht037-implies-term
         (list 'equal 'x (ht037-quoted zero))
         (list 'equal inv-x (ht037-quoted zero)))
        (ht037-implies-term
         (ht037-not-term
          (list 'equal 'x (ht037-quoted zero)))
         (list 'equal
               (ht037-static-apply-term multiply (list 'x inv-x))
               (ht037-quoted one)))))))))

(defun ht037-field-p
    (carrier zero one add multiply negate inverse)
  (let ((laws
         (ht037-field-laws-function
          carrier zero one add multiply negate inverse)))
    (and
     (tamep-functionp carrier)
     (tamep-functionp add)
     (tamep-functionp multiply)
     (tamep-functionp negate)
     (tamep-functionp inverse)
     (ht037-member-p carrier zero)
     (ht037-member-p carrier one)
     (not (equal zero one))
     (ht037-universal-p laws '(x y z)))))

(defun ht037-all-members-p (carrier objects)
  (if (consp objects)
      (and (ht037-member-p carrier (car objects))
           (ht037-all-members-p carrier (cdr objects)))
    t))

;; Field arithmetic used by the statement.

(defun ht037-add (add x y)
  (ht037-value2 add x y))

(defun ht037-mul (multiply x y)
  (ht037-value2 multiply x y))

(defun ht037-neg (negate x)
  (ht037-value1 negate x))

(defun ht037-inv (inverse x)
  (ht037-value1 inverse x))

(defun ht037-sub (add negate x y)
  (ht037-add add x (ht037-neg negate y)))

(defun ht037-div (multiply inverse x y)
  (ht037-mul multiply x (ht037-inv inverse y)))

(defun ht037-square (multiply x)
  (ht037-mul multiply x x))

(defun ht037-cube (multiply x)
  (ht037-mul multiply x (ht037-square multiply x)))

(defun ht037-two (add one)
  (ht037-add add one one))

(defun ht037-three (add one)
  (ht037-add add (ht037-two add one) one))

(defun ht037-nine (add multiply one)
  (ht037-square multiply (ht037-three add one)))

(defun ht037-twenty-seven (add multiply one)
  (ht037-mul
   multiply
   (ht037-nine add multiply one)
   (ht037-three add one)))

(defun ht037-fifty-four (add multiply one)
  (ht037-mul
   multiply
   (ht037-two add one)
   (ht037-twenty-seven add multiply one)))

(defun ht037-cardano-p
    (add multiply negate inverse a b c one)
  (let* ((three (ht037-three add one))
         (nine (ht037-nine add multiply one))
         (numerator
          (ht037-sub
           add negate
           (ht037-mul
            multiply
            (ht037-mul multiply three a)
            c)
           (ht037-square multiply b)))
         (denominator
          (ht037-mul
           multiply nine (ht037-square multiply a))))
    (ht037-div multiply inverse numerator denominator)))

(defun ht037-cardano-q
    (add multiply negate inverse a b c d one)
  (let* ((two (ht037-two add one))
         (nine (ht037-nine add multiply one))
         (twenty-seven
          (ht037-twenty-seven add multiply one))
         (fifty-four
          (ht037-fifty-four add multiply one))
         (a-squared (ht037-square multiply a))
         (a-cubed (ht037-cube multiply a))
         (b-cubed (ht037-cube multiply b))
         (nine-a-b-c
          (ht037-mul
           multiply
           (ht037-mul
            multiply
            (ht037-mul multiply nine a)
            b)
           c))
         (two-b-cubed
          (ht037-mul multiply two b-cubed))
         (twenty-seven-a-squared-d
          (ht037-mul
           multiply
           (ht037-mul multiply twenty-seven a-squared)
           d))
         (numerator
          (ht037-sub
           add negate
           (ht037-sub add negate nine-a-b-c two-b-cubed)
           twenty-seven-a-squared-d))
         (denominator
          (ht037-mul multiply fifty-four a-cubed)))
    (ht037-div multiply inverse numerator denominator)))

(defun ht037-cubic-value (add multiply a b c d x)
  (ht037-add
   add
   (ht037-add
    add
    (ht037-add
     add
     (ht037-mul multiply a (ht037-cube multiply x))
     (ht037-mul multiply b (ht037-square multiply x)))
    (ht037-mul multiply c x))
   d))

(defun ht037-primitive-cube-root-p (multiply omega one)
  (and (equal (ht037-cube multiply omega) one)
       (not (equal omega one))))

(defun ht037-base-p
    (carrier zero one add multiply negate inverse
             a b c d omega p q s x)
  (let ((two (ht037-two add one))
        (three (ht037-three add one)))
    (and
     (ht037-field-p
      carrier zero one add multiply negate inverse)
     (ht037-all-members-p
      carrier (list a b c d omega p q s x))
     (not (equal a zero))
     (not (equal two zero))
     (not (equal three zero))
     (ht037-primitive-cube-root-p multiply omega one)
     (equal
      p
      (ht037-cardano-p
       add multiply negate inverse a b c one))
     (equal
      q
      (ht037-cardano-q
       add multiply negate inverse a b c d one)))))

(defun ht037-root-characterization-p
    (zero one add multiply negate inverse
          a b c d omega p s tau x)
  (let* ((three (ht037-three add one))
         (shift
          (ht037-div
           multiply inverse b (ht037-mul multiply three a)))
         (omega-squared (ht037-square multiply omega))
         (root-one
          (if (equal p zero)
              (ht037-sub add negate s shift)
            (ht037-sub
             add negate
             (ht037-sub add negate s tau)
             shift)))
         (root-two
          (if (equal p zero)
              (ht037-sub
               add negate
               (ht037-mul multiply s omega)
               shift)
            (ht037-sub
             add negate
             (ht037-sub
              add negate
              (ht037-mul multiply s omega)
              (ht037-mul multiply tau omega-squared))
             shift)))
         (root-three
          (if (equal p zero)
              (ht037-sub
               add negate
               (ht037-mul multiply s omega-squared)
               shift)
            (ht037-sub
             add negate
             (ht037-sub
              add negate
              (ht037-mul multiply s omega-squared)
              (ht037-mul multiply tau omega))
             shift))))
    (equal
     (equal
      (ht037-cubic-value add multiply a b c d x)
      zero)
     (or (equal x root-one)
         (equal x root-two)
         (equal x root-three)))))

(defun hundred-theorems-037-solution-of-a-cubic-statement
    (carrier zero one add multiply negate inverse
             a b c d omega p q r s tau x)
  (implies
   (ht037-base-p
    carrier zero one add multiply negate inverse
    a b c d omega p q s x)
   (if (equal p zero)
       (implies
        (equal
         (ht037-cube multiply s)
         (ht037-mul multiply (ht037-two add one) q))
        (ht037-root-characterization-p
         zero one add multiply negate inverse
         a b c d omega p s tau x))
     (implies
      (and
       (ht037-member-p carrier r)
       (ht037-member-p carrier tau)
       (equal
        (ht037-square multiply r)
        (ht037-add
         add
         (ht037-square multiply q)
         (ht037-cube multiply p)))
       (equal
        (ht037-cube multiply s)
        (ht037-add add q r))
       (equal (ht037-mul multiply tau s) p))
      (ht037-root-characterization-p
       zero one add multiply negate inverse
       a b c d omega p s tau x)))))

;; Admission-time audit for the reified universal field-law function.

(defun ht037-reified-field-function-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp (ht037-true-function '(x)))
     (tamep-functionp
      (ht037-field-laws-function
       unary 0 1 binary binary unary unary)))))

(value-triple
 (if (ht037-reified-field-function-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'ht037-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
