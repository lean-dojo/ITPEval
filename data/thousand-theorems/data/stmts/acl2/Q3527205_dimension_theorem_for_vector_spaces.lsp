;; Statement-only formalization of thousand-theorems corpus artifact Q3527205,
;; "Dimension theorem for vector spaces": any two bases of the same module
;; over a semiring with invariant basis number have equinumerous index types.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, operations, and maps are tame APPLY$ function objects.
;; DEFUN-SK keeps all element, finite-free-module, and bijection quantifiers
;; inside the statement.

(defun q3527205-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun q3527205-unary-value (function object)
  (apply$ function (list object)))

(defun q3527205-binary-value (function left right)
  (apply$ function (list left right)))

;; Semirings, including the trivial semiring allowed by Lean's Semiring class.

(defun-sk q3527205-semiring-laws-p
    (carrier zero one add multiply)
  (forall (x y z)
    (implies
     (and
      (q3527205-member-p carrier x)
      (q3527205-member-p carrier y)
      (q3527205-member-p carrier z))
     (and
      (q3527205-member-p
       carrier (q3527205-binary-value add x y))
      (q3527205-member-p
       carrier (q3527205-binary-value multiply x y))
      (equal
       (q3527205-binary-value
        add (q3527205-binary-value add x y) z)
       (q3527205-binary-value
        add x (q3527205-binary-value add y z)))
      (equal
       (q3527205-binary-value add x y)
       (q3527205-binary-value add y x))
      (equal (q3527205-binary-value add x zero) x)
      (equal
       (q3527205-binary-value
        multiply (q3527205-binary-value multiply x y) z)
       (q3527205-binary-value
        multiply x (q3527205-binary-value multiply y z)))
      (equal (q3527205-binary-value multiply one x) x)
      (equal (q3527205-binary-value multiply x one) x)
      (equal
       (q3527205-binary-value
        multiply x (q3527205-binary-value add y z))
       (q3527205-binary-value
        add
        (q3527205-binary-value multiply x y)
        (q3527205-binary-value multiply x z)))
      (equal
       (q3527205-binary-value
        multiply (q3527205-binary-value add x y) z)
       (q3527205-binary-value
        add
        (q3527205-binary-value multiply x z)
        (q3527205-binary-value multiply y z)))
      (equal (q3527205-binary-value multiply zero x) zero)
      (equal (q3527205-binary-value multiply x zero) zero)))))

(defun q3527205-semiring-p
    (carrier zero one add multiply)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (q3527205-member-p carrier zero)
   (q3527205-member-p carrier one)
   (q3527205-semiring-laws-p
    carrier zero one add multiply)))

;; Additive commutative monoids with a semiring action.

(defun-sk q3527205-module-laws-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add smul)
  (forall (a b u v w)
    (and
     (implies
      (and
       (q3527205-member-p carrier u)
       (q3527205-member-p carrier v)
       (q3527205-member-p carrier w))
      (and
       (q3527205-member-p
        carrier (q3527205-binary-value add u v))
       (equal
        (q3527205-binary-value
         add (q3527205-binary-value add u v) w)
        (q3527205-binary-value
         add u (q3527205-binary-value add v w)))
       (equal
        (q3527205-binary-value add u v)
        (q3527205-binary-value add v u))
       (equal (q3527205-binary-value add u zero) u)))
     (implies
      (and
       (q3527205-member-p scalar-carrier a)
       (q3527205-member-p scalar-carrier b)
       (q3527205-member-p carrier u)
       (q3527205-member-p carrier v))
      (and
       (q3527205-member-p
        carrier (q3527205-binary-value smul a u))
       (equal
        (q3527205-binary-value smul scalar-one u)
        u)
       (equal
        (q3527205-binary-value
         smul (q3527205-binary-value scalar-multiply a b) u)
        (q3527205-binary-value
         smul a (q3527205-binary-value smul b u)))
       (equal
        (q3527205-binary-value
         smul (q3527205-binary-value scalar-add a b) u)
        (q3527205-binary-value
         add
         (q3527205-binary-value smul a u)
         (q3527205-binary-value smul b u)))
       (equal
        (q3527205-binary-value
         smul a (q3527205-binary-value add u v))
        (q3527205-binary-value
         add
         (q3527205-binary-value smul a u)
         (q3527205-binary-value smul a v)))
       (equal
        (q3527205-binary-value smul a zero)
        zero)
       (equal
        (q3527205-binary-value smul scalar-zero u)
        zero))))))

(defun q3527205-module-p
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     carrier zero add smul)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp smul)
   (q3527205-member-p carrier zero)
   (q3527205-module-laws-p
    scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
    carrier zero add smul)))

;; A canonical finite-support coordinate vector is a sorted list of
;; (index coefficient) pairs with distinct indices and nonzero coefficients.

(defun q3527205-sparse-entry-p
    (entry index-carrier scalar-carrier scalar-zero)
  (and
   (true-listp entry)
   (equal (len entry) 2)
   (q3527205-member-p index-carrier (nth 0 entry))
   (q3527205-member-p scalar-carrier (nth 1 entry))
   (not (equal (nth 1 entry) scalar-zero))))

(defun q3527205-sparse-entries-p
    (entries index-carrier scalar-carrier scalar-zero)
  (if (consp entries)
      (and
       (q3527205-sparse-entry-p
        (car entries) index-carrier scalar-carrier scalar-zero)
       (q3527205-sparse-entries-p
        (cdr entries) index-carrier scalar-carrier scalar-zero))
    (equal entries nil)))

(defun q3527205-sparse-sorted-p (entries)
  (if (and (consp entries) (consp (cdr entries)))
      (and
       (not
        (equal
         (nth 0 (car entries))
         (nth 0 (cadr entries))))
       (lexorder
        (nth 0 (car entries))
        (nth 0 (cadr entries)))
       (q3527205-sparse-sorted-p (cdr entries)))
    t))

(defun q3527205-sparse-vector-p
    (vector index-carrier scalar-carrier scalar-zero)
  (and
   (true-listp vector)
   (q3527205-sparse-entries-p
    vector index-carrier scalar-carrier scalar-zero)
   (no-duplicatesp-equal (strip-cars vector))
   (q3527205-sparse-sorted-p vector)))

(defun q3527205-coordinate-value
    (vector index scalar-zero)
  (let ((entry (assoc-equal index vector)))
    (if entry (nth 1 entry) scalar-zero)))

;; A basis package is (index-carrier coordinates realize).  COORDINATES and
;; REALIZE are inverse maps between the module and canonical finite-support
;; coordinate vectors, and COORDINATES is linear.

(defun q3527205-basis-index-carrier (basis)
  (nth 0 basis))

(defun q3527205-basis-coordinates (basis)
  (nth 1 basis))

(defun q3527205-basis-realize (basis)
  (nth 2 basis))

(defun-sk q3527205-basis-laws-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul
     index-carrier coordinates realize)
  (forall (a u v coordinate index)
    (and
     (equal
      (q3527205-unary-value coordinates module-zero)
      nil)
     (implies
      (q3527205-member-p module-carrier u)
      (and
       (q3527205-sparse-vector-p
        (q3527205-unary-value coordinates u)
        index-carrier scalar-carrier scalar-zero)
       (equal
        (q3527205-unary-value
         realize (q3527205-unary-value coordinates u))
        u)))
     (implies
      (q3527205-sparse-vector-p
       coordinate index-carrier scalar-carrier scalar-zero)
      (and
       (q3527205-member-p
        module-carrier
        (q3527205-unary-value realize coordinate))
       (equal
        (q3527205-unary-value
         coordinates
         (q3527205-unary-value realize coordinate))
        coordinate)))
     (implies
      (and
       (q3527205-member-p module-carrier u)
       (q3527205-member-p module-carrier v)
       (q3527205-member-p index-carrier index))
      (equal
       (q3527205-coordinate-value
        (q3527205-unary-value
         coordinates
         (q3527205-binary-value module-add u v))
        index scalar-zero)
       (q3527205-binary-value
        scalar-add
        (q3527205-coordinate-value
         (q3527205-unary-value coordinates u)
         index scalar-zero)
        (q3527205-coordinate-value
         (q3527205-unary-value coordinates v)
         index scalar-zero))))
     (implies
      (and
       (q3527205-member-p scalar-carrier a)
       (q3527205-member-p module-carrier u)
       (q3527205-member-p index-carrier index))
      (equal
       (q3527205-coordinate-value
        (q3527205-unary-value
         coordinates
         (q3527205-binary-value module-smul a u))
        index scalar-zero)
       (q3527205-binary-value
        scalar-multiply
        a
        (q3527205-coordinate-value
         (q3527205-unary-value coordinates u)
         index scalar-zero)))))))

(defun q3527205-basis-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul basis)
  (let ((index-carrier
         (q3527205-basis-index-carrier basis))
        (coordinates
         (q3527205-basis-coordinates basis))
        (realize
         (q3527205-basis-realize basis)))
    (and
     (true-listp basis)
     (equal (len basis) 3)
     (tamep-functionp index-carrier)
     (tamep-functionp coordinates)
     (tamep-functionp realize)
     (q3527205-basis-laws-p
      scalar-carrier scalar-zero scalar-add scalar-multiply
      module-carrier module-zero module-add module-smul
      index-carrier coordinates realize))))

;; Finite free modules R^N are canonical scalar lists of length N.

(defun q3527205-all-members-p (carrier objects)
  (if (consp objects)
      (and
       (q3527205-member-p carrier (car objects))
       (q3527205-all-members-p carrier (cdr objects)))
    (equal objects nil)))

(defun q3527205-scalar-vector-p
    (vector length scalar-carrier)
  (and
   (natp length)
   (true-listp vector)
   (equal (len vector) length)
   (q3527205-all-members-p scalar-carrier vector)))

(defun q3527205-zero-vector (length scalar-zero)
  (if (zp length)
      nil
    (cons
     scalar-zero
     (q3527205-zero-vector (- length 1) scalar-zero))))

(defun q3527205-vector-add (add left right)
  (if (and (consp left) (consp right))
      (cons
       (q3527205-binary-value add (car left) (car right))
       (q3527205-vector-add add (cdr left) (cdr right)))
    nil))

(defun q3527205-vector-smul (multiply scalar vector)
  (if (consp vector)
      (cons
       (q3527205-binary-value multiply scalar (car vector))
       (q3527205-vector-smul multiply scalar (cdr vector)))
    nil))

(defun-sk q3527205-finite-linear-equiv-laws-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply
     source-length target-length forward inverse)
  (forall (a x z y w)
    (and
     (implies
      (q3527205-scalar-vector-p
       x source-length scalar-carrier)
      (and
       (q3527205-scalar-vector-p
        (q3527205-unary-value forward x)
        target-length scalar-carrier)
       (equal
        (q3527205-unary-value
         inverse (q3527205-unary-value forward x))
        x)))
     (implies
      (q3527205-scalar-vector-p
       y target-length scalar-carrier)
      (and
       (q3527205-scalar-vector-p
        (q3527205-unary-value inverse y)
        source-length scalar-carrier)
       (equal
        (q3527205-unary-value
         forward (q3527205-unary-value inverse y))
        y)))
     (implies
      (and
       (q3527205-scalar-vector-p
        x source-length scalar-carrier)
       (q3527205-scalar-vector-p
        z source-length scalar-carrier))
      (equal
       (q3527205-unary-value
        forward (q3527205-vector-add scalar-add x z))
       (q3527205-vector-add
        scalar-add
        (q3527205-unary-value forward x)
        (q3527205-unary-value forward z))))
     (implies
      (and
       (q3527205-scalar-vector-p
        y target-length scalar-carrier)
       (q3527205-scalar-vector-p
        w target-length scalar-carrier))
      (equal
       (q3527205-unary-value
        inverse (q3527205-vector-add scalar-add y w))
       (q3527205-vector-add
        scalar-add
        (q3527205-unary-value inverse y)
        (q3527205-unary-value inverse w))))
     (implies
      (and
       (q3527205-member-p scalar-carrier a)
       (q3527205-scalar-vector-p
        x source-length scalar-carrier))
      (equal
       (q3527205-unary-value
        forward
        (q3527205-vector-smul scalar-multiply a x))
       (q3527205-vector-smul
        scalar-multiply a
        (q3527205-unary-value forward x))))
     (implies
      (and
       (q3527205-member-p scalar-carrier a)
       (q3527205-scalar-vector-p
        y target-length scalar-carrier))
      (equal
       (q3527205-unary-value
        inverse
        (q3527205-vector-smul scalar-multiply a y))
       (q3527205-vector-smul
        scalar-multiply a
        (q3527205-unary-value inverse y)))))))

(defun q3527205-finite-linear-equiv-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply
     source-length target-length forward inverse)
  (and
   (natp source-length)
   (natp target-length)
   (tamep-functionp forward)
   (tamep-functionp inverse)
   (q3527205-finite-linear-equiv-laws-p
    scalar-carrier scalar-zero scalar-add scalar-multiply
    source-length target-length forward inverse)))

;; Invariant basis number: linearly equivalent finite free modules R^M and
;; R^N have equal finite ranks.

(defun-sk q3527205-invariant-basis-number-p
    (scalar-carrier scalar-zero scalar-add scalar-multiply)
  (forall (m n forward inverse)
    (implies
     (q3527205-finite-linear-equiv-p
      scalar-carrier scalar-zero scalar-add scalar-multiply
      m n forward inverse)
     (equal m n))))

;; Lifted cardinal equality is the internal existence of a bijection between
;; the two arbitrary index carriers.

(defun-sk q3527205-bijection-laws-p
    (source target forward inverse)
  (forall (x y)
    (and
     (implies
      (q3527205-member-p source x)
      (and
       (q3527205-member-p
        target (q3527205-unary-value forward x))
       (equal
        (q3527205-unary-value
         inverse (q3527205-unary-value forward x))
        x)))
     (implies
      (q3527205-member-p target y)
      (and
       (q3527205-member-p
        source (q3527205-unary-value inverse y))
       (equal
        (q3527205-unary-value
         forward (q3527205-unary-value inverse y))
        y))))))

(defun q3527205-bijection-p
    (source target forward inverse)
  (and
   (tamep-functionp source)
   (tamep-functionp target)
   (tamep-functionp forward)
   (tamep-functionp inverse)
   (q3527205-bijection-laws-p
    source target forward inverse)))

(defun-sk q3527205-bijection-exists-p (source target)
  (exists (forward inverse)
    (q3527205-bijection-p
     source target forward inverse)))

(defun thousand-theorems-q3527205-dimension-theorem-statement
    (scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul
     basis-left basis-right)
  (implies
   (and
    (q3527205-semiring-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply)
    (q3527205-invariant-basis-number-p
     scalar-carrier scalar-zero scalar-add scalar-multiply)
    (q3527205-module-p
     scalar-carrier scalar-zero scalar-one scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul)
    (q3527205-basis-p
     scalar-carrier scalar-zero scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul basis-left)
    (q3527205-basis-p
     scalar-carrier scalar-zero scalar-add scalar-multiply
     module-carrier module-zero module-add module-smul basis-right))
   (q3527205-bijection-exists-p
    (q3527205-basis-index-carrier basis-left)
    (q3527205-basis-index-carrier basis-right))))

(value-triple :itpeval-statement-checked)
:q
