;; Statement-only formalization of thousand-theorems corpus artifact Q193878,
;; "Chinese remainder theorem": pairwise coprime ideals in a commutative ring
;; give the canonical ring equivalence from the quotient by their intersection
;; to the product of the individual quotient rings. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite index type is transported along a bijection to a duplicate-free
;; list. The aligned IDEALS list therefore represents the complete ideal
;; family without restricting the ring carrier. Ring operations and ideal
;; predicates remain arbitrary tame APPLY$ function objects.
;;
;; Quotients are represented exactly by congruence of ring representatives.
;; The canonical map sends one representative to the same representative in
;; every coordinate. Its preservation of zero, one, addition, and
;; multiplication is definitional, so being a ring equivalence reduces to
;; reflecting quotient equality and being surjective.

(defun q193878-member-p (predicate object)
  (if (apply$ predicate (list object))
      t
    nil))

;; Exact commutative-ring laws on an arbitrary carrier. Trivial rings are
;; allowed, as in the Lean CommRing hypothesis.

(defun-sk q193878-commutative-ring-laws-p
    (carrier zero one add multiply negate)
  (forall (x y z)
    (and
     (implies
      (q193878-member-p carrier x)
      (and
       (q193878-member-p
        carrier
        (apply$ negate (list x)))
       (equal
        (apply$ add (list x zero))
        x)
       (equal
        (apply$ add (list zero x))
        x)
       (equal
        (apply$ add (list x (apply$ negate (list x))))
        zero)
       (equal
        (apply$ add (list (apply$ negate (list x)) x))
        zero)
       (equal
        (apply$ multiply (list x one))
        x)
       (equal
        (apply$ multiply (list one x))
        x)))
     (implies
      (and
       (q193878-member-p carrier x)
       (q193878-member-p carrier y))
      (and
       (q193878-member-p
        carrier
        (apply$ add (list x y)))
       (q193878-member-p
        carrier
        (apply$ multiply (list x y)))
       (equal
        (apply$ add (list x y))
        (apply$ add (list y x)))
       (equal
        (apply$ multiply (list x y))
        (apply$ multiply (list y x)))))
     (implies
      (and
       (q193878-member-p carrier x)
       (q193878-member-p carrier y)
       (q193878-member-p carrier z))
      (and
       (equal
        (apply$ add
                (list (apply$ add (list x y)) z))
        (apply$ add
                (list x (apply$ add (list y z)))))
       (equal
        (apply$ multiply
                (list (apply$ multiply (list x y)) z))
        (apply$ multiply
                (list x (apply$ multiply (list y z)))))
       (equal
        (apply$ multiply
                (list x (apply$ add (list y z))))
        (apply$ add
                (list (apply$ multiply (list x y))
                      (apply$ multiply (list x z)))))
       (equal
        (apply$ multiply
                (list (apply$ add (list x y)) z))
        (apply$ add
                (list (apply$ multiply (list x z))
                      (apply$ multiply (list y z))))))))))

(defun q193878-commutative-ring-p
    (carrier zero one add multiply negate)
  (and
   (tamep-functionp carrier)
   (tamep-functionp add)
   (tamep-functionp multiply)
   (tamep-functionp negate)
   (q193878-member-p carrier zero)
   (q193878-member-p carrier one)
   (q193878-commutative-ring-laws-p
    carrier zero one add multiply negate)))

;; An ideal is an arbitrary predicate contained in the carrier, containing
;; zero, closed under addition and negation, and absorbing multiplication.

(defun-sk q193878-ideal-laws-p
    (carrier add multiply negate ideal)
  (forall (x y)
    (and
     (implies
      (q193878-member-p ideal x)
      (and
       (q193878-member-p carrier x)
       (q193878-member-p
        ideal
        (apply$ negate (list x)))))
     (implies
      (and
       (q193878-member-p ideal x)
       (q193878-member-p ideal y))
      (q193878-member-p
       ideal
       (apply$ add (list x y))))
     (implies
      (and
       (q193878-member-p carrier x)
       (q193878-member-p ideal y))
      (q193878-member-p
       ideal
       (apply$ multiply (list x y)))))))

(defun q193878-ideal-p
    (carrier zero add multiply negate ideal)
  (and
   (tamep-functionp ideal)
   (q193878-member-p ideal zero)
   (q193878-ideal-laws-p
    carrier add multiply negate ideal)))

(defun q193878-ideal-family-p
    (carrier zero add multiply negate ideals)
  (if (consp ideals)
      (and
       (q193878-ideal-p
        carrier zero add multiply negate (car ideals))
       (q193878-ideal-family-p
        carrier zero add multiply negate (cdr ideals)))
    (equal ideals nil)))

;; Two ideals are coprime exactly when their sum contains one.

(defun-sk q193878-coprime-p (left right one add)
  (exists (left-element right-element)
    (and
     (q193878-member-p left left-element)
     (q193878-member-p right right-element)
     (equal
      (apply$ add (list left-element right-element))
      one))))

(defun q193878-coprime-with-list-p
    (ideal remaining one add)
  (if (consp remaining)
      (and
       (q193878-coprime-p
        ideal (car remaining) one add)
       (q193878-coprime-with-list-p
        ideal (cdr remaining) one add))
    (equal remaining nil)))

(defun q193878-pairwise-coprime-p (ideals one add)
  (if (consp ideals)
      (and
       (q193878-coprime-with-list-p
        (car ideals) (cdr ideals) one add)
       (q193878-pairwise-coprime-p
        (cdr ideals) one add))
    (equal ideals nil)))

;; Equality in the quotient by the intersection, and equality of all
;; coordinate images in the product of quotient rings.

(defun q193878-all-ideals-contain-p (ideals object)
  (if (consp ideals)
      (and
       (q193878-member-p (car ideals) object)
       (q193878-all-ideals-contain-p
        (cdr ideals) object))
    (equal ideals nil)))

(defun q193878-intersection-congruent-p
    (ideals add negate left right)
  (q193878-all-ideals-contain-p
   ideals
   (apply$
    add
    (list left (apply$ negate (list right))))))

(defun q193878-product-images-congruent-p
    (ideals add negate left right)
  (q193878-all-ideals-contain-p
   ideals
   (apply$
    add
    (list left (apply$ negate (list right))))))

(defun-sk q193878-canonical-reflects-equality-p
    (carrier ideals add negate)
  (forall (left right)
    (implies
     (and
      (q193878-member-p carrier left)
      (q193878-member-p carrier right))
     (iff
      (q193878-intersection-congruent-p
       ideals add negate left right)
      (q193878-product-images-congruent-p
       ideals add negate left right)))))

;; Every element of the finite product of quotient rings has an aligned list
;; of representatives. Surjectivity says that one ring element is congruent
;; to each representative modulo the corresponding ideal.

(defun q193878-all-carrier-members-p (carrier values)
  (if (consp values)
      (and
       (q193878-member-p carrier (car values))
       (q193878-all-carrier-members-p
        carrier (cdr values)))
    (equal values nil)))

(defun q193878-coordinate-congruent-p
    (ideals values add negate representative)
  (if (consp ideals)
      (and
       (consp values)
       (q193878-member-p
        (car ideals)
        (apply$
         add
         (list
          representative
          (apply$ negate (list (car values))))))
       (q193878-coordinate-congruent-p
        (cdr ideals)
        (cdr values)
        add
        negate
        representative))
    (equal values nil)))

(defun-sk q193878-solution-exists-p
    (carrier ideals values add negate)
  (exists (representative)
    (and
     (q193878-member-p carrier representative)
     (q193878-coordinate-congruent-p
      ideals values add negate representative))))

(defun-sk q193878-canonical-surjective-p
    (carrier ideals add negate)
  (forall (values)
    (implies
     (and
      (true-listp values)
      (equal (len values) (len ideals))
      (q193878-all-carrier-members-p carrier values))
     (q193878-solution-exists-p
      carrier ideals values add negate))))

(defun q193878-canonical-quotient-ring-equivalence-p
    (carrier ideals add negate)
  (and
   (q193878-canonical-reflects-equality-p
    carrier ideals add negate)
   (q193878-canonical-surjective-p
    carrier ideals add negate)))

(defun thousand-theorems-q193878-chinese-remainder-theorem-statement
    (indices ideals carrier zero one add multiply negate)
  (implies
   (and
    (true-listp indices)
    (no-duplicatesp-equal indices)
    (true-listp ideals)
    (equal (len indices) (len ideals))
    (q193878-commutative-ring-p
     carrier zero one add multiply negate)
    (q193878-ideal-family-p
     carrier zero add multiply negate ideals)
    (q193878-pairwise-coprime-p
     ideals one add))
   (q193878-canonical-quotient-ring-equivalence-p
    carrier ideals add negate)))

(value-triple :itpeval-statement-checked)
:q
