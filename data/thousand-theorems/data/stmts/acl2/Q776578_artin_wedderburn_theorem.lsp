;; Statement-only formalization of thousand-theorems corpus artifact Q776578,
;; "Artin–Wedderburn theorem": every semisimple algebra over a commutative
;; semiring is algebra-equivalent to a finite product of nonzero square matrix
;; algebras over division algebras. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent arbitrary carriers and operations without
;; enumerating them. Finite products and matrices are represented by nested
;; true lists, which are extensionally equivalent to functions on Fin n.

(defun q776578-app1 (function x)
  (apply$ function (list x)))

(defun q776578-app2 (function x y)
  (apply$ function (list x y)))

(defun q776578-app3 (function x y z)
  (apply$ function (list x y z)))

(defun q776578-member-p (carrier value)
  (if (q776578-app1 carrier value) t nil))

;; The commutative-semiring base and the possibly noncommutative ring.

(defun-sk q776578-commutative-semiring-laws-p
    (carrier zero one addition multiplication)
  (forall (x y z)
    (and
     (implies
      (q776578-member-p carrier x)
      (and
       (equal (q776578-app2 addition x zero) x)
       (equal (q776578-app2 addition zero x) x)
       (equal (q776578-app2 multiplication x one) x)
       (equal (q776578-app2 multiplication one x) x)
       (equal (q776578-app2 multiplication x zero) zero)
       (equal (q776578-app2 multiplication zero x) zero)))
     (implies
      (and
       (q776578-member-p carrier x)
       (q776578-member-p carrier y))
      (and
       (q776578-member-p carrier
                         (q776578-app2 addition x y))
       (q776578-member-p carrier
                         (q776578-app2 multiplication x y))
       (equal (q776578-app2 addition x y)
              (q776578-app2 addition y x))
       (equal (q776578-app2 multiplication x y)
              (q776578-app2 multiplication y x))))
     (implies
      (and
       (q776578-member-p carrier x)
       (q776578-member-p carrier y)
       (q776578-member-p carrier z))
      (and
       (equal
        (q776578-app2 addition
                      (q776578-app2 addition x y)
                      z)
        (q776578-app2 addition
                      x
                      (q776578-app2 addition y z)))
       (equal
        (q776578-app2 multiplication
                      (q776578-app2 multiplication x y)
                      z)
        (q776578-app2 multiplication
                      x
                      (q776578-app2 multiplication y z)))
       (equal
        (q776578-app2 multiplication
                      x
                      (q776578-app2 addition y z))
        (q776578-app2 addition
                      (q776578-app2 multiplication x y)
                      (q776578-app2 multiplication x z)))
       (equal
        (q776578-app2 multiplication
                      (q776578-app2 addition x y)
                      z)
        (q776578-app2 addition
                      (q776578-app2 multiplication x z)
                      (q776578-app2 multiplication y z))))))))

(defun q776578-commutative-semiring-p
    (carrier zero one addition multiplication)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (q776578-member-p carrier zero)
   (q776578-member-p carrier one)
   (q776578-commutative-semiring-laws-p
    carrier zero one addition multiplication)))

(defun-sk q776578-ring-laws-p
    (carrier zero one addition multiplication negation)
  (forall (x y z)
    (and
     (implies
      (q776578-member-p carrier x)
      (and
       (q776578-member-p carrier (q776578-app1 negation x))
       (equal (q776578-app2 addition x zero) x)
       (equal (q776578-app2 addition zero x) x)
       (equal
        (q776578-app2 addition x (q776578-app1 negation x))
        zero)
       (equal
        (q776578-app2 addition (q776578-app1 negation x) x)
        zero)
       (equal (q776578-app2 multiplication x one) x)
       (equal (q776578-app2 multiplication one x) x)
       (equal (q776578-app2 multiplication x zero) zero)
       (equal (q776578-app2 multiplication zero x) zero)))
     (implies
      (and
       (q776578-member-p carrier x)
       (q776578-member-p carrier y))
      (and
       (q776578-member-p carrier
                         (q776578-app2 addition x y))
       (q776578-member-p carrier
                         (q776578-app2 multiplication x y))
       (equal (q776578-app2 addition x y)
              (q776578-app2 addition y x))))
     (implies
      (and
       (q776578-member-p carrier x)
       (q776578-member-p carrier y)
       (q776578-member-p carrier z))
      (and
       (equal
        (q776578-app2 addition
                      (q776578-app2 addition x y)
                      z)
        (q776578-app2 addition
                      x
                      (q776578-app2 addition y z)))
       (equal
        (q776578-app2 multiplication
                      (q776578-app2 multiplication x y)
                      z)
        (q776578-app2 multiplication
                      x
                      (q776578-app2 multiplication y z)))
       (equal
        (q776578-app2 multiplication
                      x
                      (q776578-app2 addition y z))
        (q776578-app2 addition
                      (q776578-app2 multiplication x y)
                      (q776578-app2 multiplication x z)))
       (equal
        (q776578-app2 multiplication
                      (q776578-app2 addition x y)
                      z)
        (q776578-app2 addition
                      (q776578-app2 multiplication x z)
                      (q776578-app2 multiplication y z))))))))

(defun q776578-ring-p
    (carrier zero one addition multiplication negation)
  (and
   (tamep-functionp carrier)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (q776578-member-p carrier zero)
   (q776578-member-p carrier one)
   (q776578-ring-laws-p
    carrier zero one addition multiplication negation)))

;; An algebra map is a unital semiring homomorphism whose image is central.

(defun-sk q776578-algebra-laws-p
    (base-carrier base-zero base-one base-add base-mul
     ring-carrier ring-zero ring-one ring-add ring-mul algebra-map)
  (forall (a b x)
    (and
     (implies
      (q776578-member-p base-carrier a)
      (and
       (q776578-member-p ring-carrier
                         (q776578-app1 algebra-map a))
       (implies
        (q776578-member-p ring-carrier x)
        (equal
         (q776578-app2 ring-mul
                       (q776578-app1 algebra-map a)
                       x)
         (q776578-app2 ring-mul
                       x
                       (q776578-app1 algebra-map a))))))
     (implies
      (and
       (q776578-member-p base-carrier a)
       (q776578-member-p base-carrier b))
      (and
       (equal
        (q776578-app1 algebra-map
                      (q776578-app2 base-add a b))
        (q776578-app2 ring-add
                      (q776578-app1 algebra-map a)
                      (q776578-app1 algebra-map b)))
       (equal
        (q776578-app1 algebra-map
                      (q776578-app2 base-mul a b))
        (q776578-app2 ring-mul
                      (q776578-app1 algebra-map a)
                      (q776578-app1 algebra-map b)))))
     (equal
      (q776578-app1 algebra-map base-zero)
      ring-zero)
     (equal
      (q776578-app1 algebra-map base-one)
      ring-one))))

(defun q776578-algebra-p
    (base-carrier base-zero base-one base-add base-mul
     ring-carrier ring-zero ring-one ring-add ring-mul algebra-map)
  (and
   (tamep-functionp algebra-map)
   (q776578-algebra-laws-p
    base-carrier base-zero base-one base-add base-mul
    ring-carrier ring-zero ring-one ring-add ring-mul algebra-map)))

;; A ring is semisimple exactly when its regular left module is semisimple;
;; equivalently, every left ideal has a complementary left ideal.

(defun-sk q776578-left-ideal-laws-p
    (carrier zero addition multiplication negation ideal)
  (forall (a x y)
    (and
     (implies
      (q776578-member-p ideal x)
      (and
       (q776578-member-p carrier x)
       (q776578-member-p ideal (q776578-app1 negation x))))
     (implies
      (and
       (q776578-member-p ideal x)
       (q776578-member-p ideal y))
      (q776578-member-p ideal
                        (q776578-app2 addition x y)))
     (implies
      (and
       (q776578-member-p carrier a)
       (q776578-member-p ideal x))
      (q776578-member-p ideal
                        (q776578-app2 multiplication a x))))))

(defun q776578-left-ideal-p
    (carrier zero addition multiplication negation ideal)
  (and
   (tamep-functionp ideal)
   (q776578-member-p ideal zero)
   (q776578-left-ideal-laws-p
    carrier zero addition multiplication negation ideal)))

(defun-sk q776578-ideal-sum-representation-p
    (addition left right value)
  (exists (left-value right-value)
    (and
     (q776578-member-p left left-value)
     (q776578-member-p right right-value)
     (equal
      (q776578-app2 addition left-value right-value)
      value))))

(defun-sk q776578-direct-complement-laws-p
    (carrier zero addition ideal complement)
  (forall (x)
    (and
     (implies
      (and
       (q776578-member-p ideal x)
       (q776578-member-p complement x))
      (equal x zero))
     (implies
      (q776578-member-p carrier x)
      (q776578-ideal-sum-representation-p
       addition ideal complement x)))))

(defun q776578-direct-complement-p
    (carrier zero addition multiplication negation ideal complement)
  (and
   (q776578-left-ideal-p
    carrier zero addition multiplication negation complement)
   (q776578-direct-complement-laws-p
    carrier zero addition ideal complement)))

(defun-sk q776578-left-ideal-complement-exists-p
    (carrier zero addition multiplication negation ideal)
  (exists (complement)
    (q776578-direct-complement-p
     carrier zero addition multiplication negation ideal complement)))

(defun-sk q776578-semisimple-ring-p
    (carrier zero addition multiplication negation)
  (forall (ideal)
    (implies
     (q776578-left-ideal-p
      carrier zero addition multiplication negation ideal)
     (q776578-left-ideal-complement-exists-p
      carrier zero addition multiplication negation ideal))))

;; The existential family D_i of division algebras and the positive dimensions.

(defun q776578-valid-index-p (index size)
  (and (natp index)
       (< index size)))

(defun-sk q776578-dimensions-laws-p (size dimensions)
  (forall (index)
    (implies
     (q776578-valid-index-p index size)
     (and
      (natp (q776578-app1 dimensions index))
      (< 0 (q776578-app1 dimensions index))))))

(defun-sk q776578-division-family-points-p
    (size carrier zero one)
  (forall (index)
    (implies
     (q776578-valid-index-p index size)
     (and
      (q776578-app2 carrier index (q776578-app1 zero index))
      (q776578-app2 carrier index (q776578-app1 one index))
      (not
       (equal
        (q776578-app1 zero index)
        (q776578-app1 one index)))))))

(defun-sk q776578-division-family-laws-p
    (size carrier zero one addition multiplication negation inverse)
  (forall (index x y z)
    (and
     (implies
      (and
       (q776578-valid-index-p index size)
       (q776578-app2 carrier index x))
      (and
       (q776578-app2 carrier index
                     (q776578-app2 negation index x))
       (q776578-app2 carrier index
                     (q776578-app2 inverse index x))
       (equal
        (q776578-app3 addition index x
                       (q776578-app1 zero index))
        x)
       (equal
        (q776578-app3 addition index
                       (q776578-app1 zero index) x)
        x)
       (equal
        (q776578-app3 addition index x
                       (q776578-app2 negation index x))
        (q776578-app1 zero index))
       (equal
        (q776578-app3 addition index
                       (q776578-app2 negation index x) x)
        (q776578-app1 zero index))
       (equal
        (q776578-app3 multiplication index x
                       (q776578-app1 one index))
        x)
       (equal
        (q776578-app3 multiplication index
                       (q776578-app1 one index) x)
        x)
       (equal
        (q776578-app3 multiplication index x
                       (q776578-app1 zero index))
        (q776578-app1 zero index))
       (equal
        (q776578-app3 multiplication index
                       (q776578-app1 zero index) x)
        (q776578-app1 zero index))
       (implies
        (equal x (q776578-app1 zero index))
        (equal
         (q776578-app2 inverse index x)
         (q776578-app1 zero index)))
       (implies
        (not (equal x (q776578-app1 zero index)))
        (and
         (equal
          (q776578-app3 multiplication index x
                           (q776578-app2 inverse index x))
          (q776578-app1 one index))
         (equal
          (q776578-app3 multiplication index
                           (q776578-app2 inverse index x) x)
          (q776578-app1 one index))))))
     (implies
      (and
       (q776578-valid-index-p index size)
       (q776578-app2 carrier index x)
       (q776578-app2 carrier index y))
      (and
       (q776578-app2 carrier index
                     (q776578-app3 addition index x y))
       (q776578-app2 carrier index
                     (q776578-app3 multiplication index x y))
       (equal
        (q776578-app3 addition index x y)
        (q776578-app3 addition index y x))))
     (implies
      (and
       (q776578-valid-index-p index size)
       (q776578-app2 carrier index x)
       (q776578-app2 carrier index y)
       (q776578-app2 carrier index z))
      (and
       (equal
        (q776578-app3 addition index
                       (q776578-app3 addition index x y) z)
        (q776578-app3 addition index
                       x (q776578-app3 addition index y z)))
       (equal
        (q776578-app3 multiplication index
                       (q776578-app3 multiplication index x y) z)
        (q776578-app3 multiplication index
                       x (q776578-app3 multiplication index y z)))
       (equal
        (q776578-app3 multiplication index
                       x (q776578-app3 addition index y z))
        (q776578-app3 addition index
                       (q776578-app3 multiplication index x y)
                       (q776578-app3 multiplication index x z)))
       (equal
        (q776578-app3 multiplication index
                       (q776578-app3 addition index x y) z)
        (q776578-app3 addition index
                       (q776578-app3 multiplication index x z)
                       (q776578-app3 multiplication index y z))))))))

(defun q776578-division-ring-family-p
    (size dimensions carrier zero one addition multiplication negation inverse)
  (and
   (natp size)
   (tamep-functionp dimensions)
   (tamep-functionp carrier)
   (tamep-functionp zero)
   (tamep-functionp one)
   (tamep-functionp addition)
   (tamep-functionp multiplication)
   (tamep-functionp negation)
   (tamep-functionp inverse)
   (q776578-dimensions-laws-p size dimensions)
   (q776578-division-family-points-p size carrier zero one)
   (q776578-division-family-laws-p
    size carrier zero one addition multiplication negation inverse)))

(defun-sk q776578-division-algebra-family-laws-p
    (size
     base-carrier base-zero base-one base-add base-mul
     carrier zero one addition multiplication algebra-map)
  (forall (index a b x)
    (and
     (implies
      (and
       (q776578-valid-index-p index size)
       (q776578-member-p base-carrier a))
      (and
       (q776578-app2 carrier index
                     (q776578-app2 algebra-map index a))
       (implies
        (q776578-app2 carrier index x)
        (equal
         (q776578-app3 multiplication index
                          (q776578-app2 algebra-map index a) x)
         (q776578-app3 multiplication index
                          x (q776578-app2 algebra-map index a))))))
     (implies
      (and
       (q776578-valid-index-p index size)
       (q776578-member-p base-carrier a)
       (q776578-member-p base-carrier b))
      (and
       (equal
        (q776578-app2 algebra-map index
                       (q776578-app2 base-add a b))
        (q776578-app3 addition index
                       (q776578-app2 algebra-map index a)
                       (q776578-app2 algebra-map index b)))
       (equal
        (q776578-app2 algebra-map index
                       (q776578-app2 base-mul a b))
        (q776578-app3 multiplication index
                       (q776578-app2 algebra-map index a)
                       (q776578-app2 algebra-map index b)))))
     (implies
      (q776578-valid-index-p index size)
      (and
       (equal
        (q776578-app2 algebra-map index base-zero)
        (q776578-app1 zero index))
       (equal
        (q776578-app2 algebra-map index base-one)
        (q776578-app1 one index)))))))

(defun q776578-division-algebra-family-p
    (size
     base-carrier base-zero base-one base-add base-mul
     carrier zero one addition multiplication algebra-map)
  (and
   (tamep-functionp algebra-map)
   (q776578-division-algebra-family-laws-p
    size
    base-carrier base-zero base-one base-add base-mul
    carrier zero one addition multiplication algebra-map)))

;; Canonical finite-list presentation of the product of square matrix rings.

(defun q776578-division-list-p (index carrier values)
  (if (consp values)
      (and
       (q776578-app2 carrier index (car values))
       (q776578-division-list-p index carrier (cdr values)))
    (equal values nil)))

(defun q776578-matrix-rows-p
    (index dimension carrier rows)
  (if (consp rows)
      (and
       (true-listp (car rows))
       (equal (len (car rows)) dimension)
       (q776578-division-list-p index carrier (car rows))
       (q776578-matrix-rows-p
        index dimension carrier (cdr rows)))
    (equal rows nil)))

(defun q776578-matrix-p
    (index dimension carrier matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) dimension)
   (q776578-matrix-rows-p
    index dimension carrier matrix)))

(defun q776578-product-p-from
    (index remaining dimensions carrier value)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal value nil)
    (and
     (consp value)
     (q776578-matrix-p
      index
      (nfix (q776578-app1 dimensions index))
      carrier
      (car value))
     (q776578-product-p-from
      (+ 1 index)
      (- remaining 1)
      dimensions
      carrier
      (cdr value)))))

(defun q776578-product-p
    (size dimensions carrier value)
  (q776578-product-p-from
   0 (nfix size) dimensions carrier value))

(defun q776578-constant-row (remaining value)
  (if (zp remaining)
      nil
    (cons value
          (q776578-constant-row (- remaining 1) value))))

(defun q776578-zero-matrix (index dimension zero)
  (if (zp dimension)
      nil
    (cons
     (q776578-constant-row
      dimension (q776578-app1 zero index))
     (q776578-zero-matrix index (- dimension 1) zero))))

(defun q776578-diagonal-row
    (index row column remaining zero one)
  (if (zp remaining)
      nil
    (cons
     (if (equal row column)
         (q776578-app1 one index)
       (q776578-app1 zero index))
     (q776578-diagonal-row
      index row (+ 1 column) (- remaining 1) zero one))))

(defun q776578-one-matrix-from-row
    (index row remaining dimension zero one)
  (if (zp remaining)
      nil
    (cons
     (q776578-diagonal-row
      index row 0 dimension zero one)
     (q776578-one-matrix-from-row
      index (+ 1 row) (- remaining 1) dimension zero one))))

(defun q776578-one-matrix (index dimension zero one)
  (q776578-one-matrix-from-row
   index 0 dimension dimension zero one))

(defun q776578-product-zero-from
    (index remaining dimensions zero)
  (if (zp remaining)
      nil
    (cons
     (q776578-zero-matrix
      index
      (nfix (q776578-app1 dimensions index))
      zero)
     (q776578-product-zero-from
      (+ 1 index) (- remaining 1) dimensions zero))))

(defun q776578-product-zero (size dimensions zero)
  (q776578-product-zero-from
   0 (nfix size) dimensions zero))

(defun q776578-product-one-from
    (index remaining dimensions zero one)
  (if (zp remaining)
      nil
    (cons
     (q776578-one-matrix
      index
      (nfix (q776578-app1 dimensions index))
      zero one)
     (q776578-product-one-from
      (+ 1 index) (- remaining 1) dimensions zero one))))

(defun q776578-product-one (size dimensions zero one)
  (q776578-product-one-from
   0 (nfix size) dimensions zero one))

(defun q776578-add-row (index addition left right)
  (if (and (consp left) (consp right))
      (cons
       (q776578-app3 addition index (car left) (car right))
       (q776578-add-row index addition (cdr left) (cdr right)))
    nil))

(defun q776578-add-matrix (index addition left right)
  (if (and (consp left) (consp right))
      (cons
       (q776578-add-row index addition (car left) (car right))
       (q776578-add-matrix
        index addition (cdr left) (cdr right)))
    nil))

(defun q776578-product-add-from
    (index remaining addition left right)
  (if (zp remaining)
      nil
    (cons
     (q776578-add-matrix
      index addition (car left) (car right))
     (q776578-product-add-from
      (+ 1 index)
      (- remaining 1)
      addition
      (cdr left)
      (cdr right)))))

(defun q776578-product-add (size addition left right)
  (q776578-product-add-from
   0 (nfix size) addition left right))

(defun q776578-dot-product-from
    (index row column term remaining left right
     zero addition multiplication)
  (if (zp remaining)
      (q776578-app1 zero index)
    (q776578-app3
     addition
     index
     (q776578-app3
      multiplication
      index
      (nth term (nth row left))
      (nth column (nth term right)))
     (q776578-dot-product-from
      index row column (+ 1 term) (- remaining 1) left right
      zero addition multiplication))))

(defun q776578-multiply-row-from
    (index row column remaining dimension left right
     zero addition multiplication)
  (if (zp remaining)
      nil
    (cons
     (q776578-dot-product-from
      index row column 0 dimension left right
      zero addition multiplication)
     (q776578-multiply-row-from
      index row (+ 1 column) (- remaining 1) dimension left right
      zero addition multiplication))))

(defun q776578-multiply-matrix-from
    (index row remaining dimension left right
     zero addition multiplication)
  (if (zp remaining)
      nil
    (cons
     (q776578-multiply-row-from
      index row 0 dimension dimension left right
      zero addition multiplication)
     (q776578-multiply-matrix-from
      index (+ 1 row) (- remaining 1) dimension left right
      zero addition multiplication))))

(defun q776578-multiply-matrix
    (index dimension left right zero addition multiplication)
  (q776578-multiply-matrix-from
   index 0 dimension dimension left right
   zero addition multiplication))

(defun q776578-product-multiply-from
    (index remaining dimensions left right
     zero addition multiplication)
  (if (zp remaining)
      nil
    (cons
     (q776578-multiply-matrix
      index
      (nfix (q776578-app1 dimensions index))
      (car left)
      (car right)
      zero addition multiplication)
     (q776578-product-multiply-from
      (+ 1 index)
      (- remaining 1)
      dimensions
      (cdr left)
      (cdr right)
      zero addition multiplication))))

(defun q776578-product-multiply
    (size dimensions left right zero addition multiplication)
  (q776578-product-multiply-from
   0 (nfix size) dimensions left right
   zero addition multiplication))

(defun q776578-algebra-diagonal-row
    (index scalar row column remaining zero algebra-map)
  (if (zp remaining)
      nil
    (cons
     (if (equal row column)
         (q776578-app2 algebra-map index scalar)
       (q776578-app1 zero index))
     (q776578-algebra-diagonal-row
      index scalar row (+ 1 column) (- remaining 1)
      zero algebra-map))))

(defun q776578-algebra-matrix-from-row
    (index scalar row remaining dimension zero algebra-map)
  (if (zp remaining)
      nil
    (cons
     (q776578-algebra-diagonal-row
      index scalar row 0 dimension zero algebra-map)
     (q776578-algebra-matrix-from-row
      index scalar (+ 1 row) (- remaining 1) dimension
      zero algebra-map))))

(defun q776578-algebra-matrix
    (index scalar dimension zero algebra-map)
  (q776578-algebra-matrix-from-row
   index scalar 0 dimension dimension zero algebra-map))

(defun q776578-product-algebra-map-from
    (index remaining scalar dimensions zero algebra-map)
  (if (zp remaining)
      nil
    (cons
     (q776578-algebra-matrix
      index scalar
      (nfix (q776578-app1 dimensions index))
      zero algebra-map)
     (q776578-product-algebra-map-from
      (+ 1 index) (- remaining 1) scalar dimensions
      zero algebra-map))))

(defun q776578-product-algebra-map
    (size scalar dimensions zero algebra-map)
  (q776578-product-algebra-map-from
   0 (nfix size) scalar dimensions zero algebra-map))

;; Forward and inverse maps give a bijective R0-algebra homomorphism.

(defun-sk q776578-algebra-equivalence-laws-p
    (size dimensions
     base-carrier
     ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map
     division-carrier division-zero division-one
     division-add division-mul division-algebra-map
     forward inverse)
  (forall (x y scalar target)
    (and
     (implies
      (q776578-member-p ring-carrier x)
      (and
       (q776578-product-p
        size dimensions division-carrier
        (q776578-app1 forward x))
       (q776578-member-p
        ring-carrier
        (q776578-app1 inverse (q776578-app1 forward x)))
       (equal
        (q776578-app1 inverse (q776578-app1 forward x))
        x)))
     (implies
      (q776578-product-p
       size dimensions division-carrier target)
      (and
       (q776578-member-p ring-carrier
                         (q776578-app1 inverse target))
       (equal
        (q776578-app1 forward (q776578-app1 inverse target))
        target)))
     (implies
      (and
       (q776578-member-p ring-carrier x)
       (q776578-member-p ring-carrier y))
      (and
       (equal
        (q776578-app1
         forward (q776578-app2 ring-add x y))
        (q776578-product-add
         size division-add
         (q776578-app1 forward x)
         (q776578-app1 forward y)))
       (equal
        (q776578-app1
         forward (q776578-app2 ring-mul x y))
        (q776578-product-multiply
         size dimensions
         (q776578-app1 forward x)
         (q776578-app1 forward y)
         division-zero division-add division-mul))))
     (equal
      (q776578-app1 forward ring-zero)
      (q776578-product-zero
       size dimensions division-zero))
     (equal
      (q776578-app1 forward ring-one)
      (q776578-product-one
       size dimensions division-zero division-one))
     (implies
      (q776578-member-p base-carrier scalar)
      (equal
       (q776578-app1
        forward (q776578-app1 ring-algebra-map scalar))
       (q776578-product-algebra-map
        size scalar dimensions division-zero division-algebra-map))))))

(defun q776578-artin-wedderburn-witness-p
    (base-carrier base-zero base-one base-add base-mul
     ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map
     size dimensions
     division-carrier division-zero division-one
     division-add division-mul division-neg division-inverse
     division-algebra-map forward inverse)
  (and
   (q776578-division-ring-family-p
    size dimensions
    division-carrier division-zero division-one
    division-add division-mul division-neg division-inverse)
   (q776578-division-algebra-family-p
    size
    base-carrier base-zero base-one base-add base-mul
    division-carrier division-zero division-one
    division-add division-mul division-algebra-map)
   (tamep-functionp forward)
   (tamep-functionp inverse)
   (q776578-algebra-equivalence-laws-p
    size dimensions
    base-carrier
    ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map
    division-carrier division-zero division-one
    division-add division-mul division-algebra-map
    forward inverse)))

(defun-sk q776578-artin-wedderburn-conclusion-p
    (base-carrier base-zero base-one base-add base-mul
     ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map)
  (exists
   (size dimensions
    division-carrier division-zero division-one
    division-add division-mul division-neg division-inverse
    division-algebra-map forward inverse)
   (q776578-artin-wedderburn-witness-p
    base-carrier base-zero base-one base-add base-mul
    ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map
    size dimensions
    division-carrier division-zero division-one
    division-add division-mul division-neg division-inverse
    division-algebra-map forward inverse)))

(defun-sk thousand-theorems-q776578-artin-wedderburn-theorem-statement ()
  (forall
   (base-carrier base-zero base-one base-add base-mul
    ring-carrier ring-zero ring-one ring-add ring-mul ring-neg
    ring-algebra-map)
   (implies
    (and
     (q776578-commutative-semiring-p
      base-carrier base-zero base-one base-add base-mul)
     (q776578-ring-p
      ring-carrier ring-zero ring-one ring-add ring-mul ring-neg)
     (q776578-algebra-p
      base-carrier base-zero base-one base-add base-mul
      ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map)
     (q776578-semisimple-ring-p
      ring-carrier ring-zero ring-add ring-mul ring-neg))
    (q776578-artin-wedderburn-conclusion-p
     base-carrier base-zero base-one base-add base-mul
     ring-carrier ring-zero ring-one ring-add ring-mul ring-algebra-map))))

(value-triple :itpeval-statement-checked)
:q
