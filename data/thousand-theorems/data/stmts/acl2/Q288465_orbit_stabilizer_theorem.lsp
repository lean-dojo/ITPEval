;; Statement-only formalization of thousand-theorems corpus artifact Q288465,
;; "Orbit-stabilizer theorem": for an arbitrary group action, the orbit of a
;; point is canonically equivalent to the quotient of the group by that
;; point's stabilizer. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Arbitrary carriers, operations, and actions are tame function objects.
;; Each unbounded quantifier is flattened to one tuple variable and checked
;; with FN-EQUAL.

(defun q288465-quoted (object)
  (list 'quote object))

(defun q288465-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q288465-term-list (cdr terms)))
    (q288465-quoted nil)))

(defun q288465-apply-term (function arguments)
  (list
   'apply$
   (q288465-quoted function)
   (q288465-term-list arguments)))

(defun q288465-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q288465-and-terms (cdr terms))
       (q288465-quoted nil))
    (q288465-quoted t)))

(defun q288465-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q288465-quoted t)))

(defun q288465-iff-term (left right)
  (list
   'if
   left
   (list
    'if
    right
    (q288465-quoted t)
    (q288465-quoted nil))
   (list
    'if
    right
    (q288465-quoted nil)
    (q288465-quoted t))))

(defun q288465-nth-term (index tuple)
  (list 'nth (q288465-quoted index) tuple))

(defun q288465-tuple-of-length-term (tuple length)
  (q288465-and-terms
   (list
    (list 'true-listp tuple)
    (list
     'equal
     (list 'len tuple)
     (q288465-quoted length)))))

(defun q288465-member-term (carrier object)
  (q288465-apply-term carrier (list object)))

(defun q288465-mul-term (multiplication left right)
  (q288465-apply-term multiplication (list left right)))

(defun q288465-inv-term (inverse object)
  (q288465-apply-term inverse (list object)))

(defun q288465-action-term (action group-element point)
  (q288465-apply-term action (list group-element point)))

(defun q288465-true-function ()
  (list 'lambda '(tuple) (q288465-quoted t)))

(defun q288465-universal-p (condition)
  (let ((always-true (q288465-true-function)))
    (and
     (tamep-functionp condition)
     (tamep-functionp always-true)
     (fn-equal condition always-true))))

(defun q288465-member-p (carrier object)
  (if (apply$ carrier (list object))
      t
    nil))

;; Group structure on the acting carrier.

(defun q288465-group-laws-function
    (carrier multiplication inverse identity)
  (let* ((x (q288465-nth-term 0 'tuple))
         (y (q288465-nth-term 1 'tuple))
         (z (q288465-nth-term 2 'tuple))
         (x-in (q288465-member-term carrier x))
         (y-in (q288465-member-term carrier y))
         (z-in (q288465-member-term carrier z))
         (inv-x (q288465-inv-term inverse x))
         (xy (q288465-mul-term multiplication x y))
         (unary-hypothesis
          (q288465-and-terms
           (list
            (q288465-tuple-of-length-term 'tuple 1)
            x-in)))
         (binary-hypothesis
          (q288465-and-terms
           (list
            (q288465-tuple-of-length-term 'tuple 2)
            x-in
            y-in)))
         (ternary-hypothesis
          (q288465-and-terms
           (list
            (q288465-tuple-of-length-term 'tuple 3)
            x-in
            y-in
            z-in))))
    (list
     'lambda
     '(tuple)
     (q288465-and-terms
      (list
       (q288465-implies-term
        unary-hypothesis
        (q288465-and-terms
         (list
          (q288465-member-term carrier inv-x)
          (list
           'equal
           (q288465-mul-term
            multiplication x (q288465-quoted identity))
           x)
          (list
           'equal
           (q288465-mul-term
            multiplication (q288465-quoted identity) x)
           x)
          (list
           'equal
           (q288465-mul-term multiplication x inv-x)
           (q288465-quoted identity))
          (list
           'equal
           (q288465-mul-term multiplication inv-x x)
           (q288465-quoted identity)))))
       (q288465-implies-term
        binary-hypothesis
        (q288465-member-term carrier xy))
       (q288465-implies-term
        ternary-hypothesis
        (list
         'equal
         (q288465-mul-term
          multiplication
          (q288465-mul-term multiplication x y)
          z)
         (q288465-mul-term
          multiplication
          x
          (q288465-mul-term multiplication y z)))))))))

(defun q288465-group-p
    (carrier multiplication inverse identity)
  (and
   (tamep-functionp carrier)
   (tamep-functionp multiplication)
   (tamep-functionp inverse)
   (q288465-member-p carrier identity)
   (q288465-universal-p
    (q288465-group-laws-function
     carrier multiplication inverse identity))))

;; Multiplicative action on an arbitrary point carrier.

(defun q288465-action-laws-function
    (group-carrier
     point-carrier
     multiplication
     identity
     action)
  (let* ((g (q288465-nth-term 0 'tuple))
         (h (q288465-nth-term 1 'tuple))
         (x (q288465-nth-term 2 'tuple))
         (unary-x (q288465-nth-term 0 'tuple))
         (g-in (q288465-member-term group-carrier g))
         (h-in (q288465-member-term group-carrier h))
         (x-in (q288465-member-term point-carrier x))
         (unary-x-in
          (q288465-member-term point-carrier unary-x))
         (binary-hypothesis
          (q288465-and-terms
           (list
            (q288465-tuple-of-length-term 'tuple 2)
            g-in
            (q288465-member-term point-carrier h))))
         (ternary-hypothesis
          (q288465-and-terms
           (list
            (q288465-tuple-of-length-term 'tuple 3)
            g-in
            h-in
            x-in))))
    (list
     'lambda
     '(tuple)
     (q288465-and-terms
      (list
       (q288465-implies-term
        (q288465-and-terms
         (list
          (q288465-tuple-of-length-term 'tuple 1)
          unary-x-in))
        (list
         'equal
         (q288465-action-term
          action
          (q288465-quoted identity)
          unary-x)
         unary-x))
       (q288465-implies-term
        binary-hypothesis
        (q288465-member-term
         point-carrier
         (q288465-action-term action g h)))
       (q288465-implies-term
        ternary-hypothesis
        (list
         'equal
         (q288465-action-term
          action
          (q288465-mul-term multiplication g h)
          x)
         (q288465-action-term
          action
          g
          (q288465-action-term action h x)))))))))

(defun q288465-action-p
    (group-carrier
     point-carrier
     multiplication
     identity
     action)
  (and
   (tamep-functionp point-carrier)
   (tamep-functionp action)
   (q288465-universal-p
    (q288465-action-laws-function
     group-carrier
     point-carrier
     multiplication
     identity
     action))))

;; The orbit is the exact range of g |-> g action base-point inside the point
;; carrier. The left-coset quotient relation for the stabilizer identifies g
;; and h exactly when g^-1*h fixes the base point.

(defun-sk q288465-orbit-member-p
    (group-carrier point-carrier action base-point point)
  (exists (g)
    (and
     (q288465-member-p point-carrier point)
     (q288465-member-p group-carrier g)
     (equal
      (apply$ action (list g base-point))
      point))))

(defun q288465-stabilizer-coset-equivalent-p
    (group-carrier multiplication inverse action base-point g h)
  (and
   (q288465-member-p group-carrier g)
   (q288465-member-p group-carrier h)
   (equal
    (apply$
     action
     (list
      (apply$
       multiplication
       (list (apply$ inverse (list g)) h))
      base-point))
    base-point)))

;; The inverse of the Lean equivalence is the canonical map [g] |-> g action
;; base-point. It maps every quotient representative into the orbit, identifies
;; exactly the representatives in the same stabilizer coset, and reaches every
;; orbit point.

(defun-sk q288465-canonical-map-into-orbit-p
    (group-carrier point-carrier action base-point)
  (forall (g)
    (implies
     (q288465-member-p group-carrier g)
     (q288465-orbit-member-p
      group-carrier
      point-carrier
      action
      base-point
      (apply$ action (list g base-point))))))

(defun-sk q288465-canonical-map-equality-p
    (group-carrier multiplication inverse action base-point)
  (forall (g h)
    (implies
     (and
      (q288465-member-p group-carrier g)
      (q288465-member-p group-carrier h))
     (iff
      (q288465-stabilizer-coset-equivalent-p
       group-carrier
       multiplication
       inverse
       action
       base-point
       g
       h)
      (equal
       (apply$ action (list g base-point))
       (apply$ action (list h base-point)))))))

(defun-sk q288465-canonical-preimage-exists-p
    (group-carrier action base-point point)
  (exists (g)
    (and
     (q288465-member-p group-carrier g)
     (equal
      (apply$ action (list g base-point))
      point))))

(defun-sk q288465-canonical-map-surjective-p
    (group-carrier point-carrier action base-point)
  (forall (point)
    (implies
     (q288465-orbit-member-p
      group-carrier point-carrier action base-point point)
     (q288465-canonical-preimage-exists-p
      group-carrier action base-point point))))

(defun q288465-canonical-orbit-quotient-equivalence-p
    (group-carrier
     point-carrier
     multiplication
     inverse
     action
     base-point)
  (and
   (q288465-canonical-map-into-orbit-p
    group-carrier point-carrier action base-point)
   (q288465-canonical-map-equality-p
    group-carrier multiplication inverse action base-point)
   (q288465-canonical-map-surjective-p
    group-carrier point-carrier action base-point)))

(defun thousand-theorems-q288465-orbit-stabilizer-theorem-statement
    (group-carrier
     point-carrier
     multiplication
     inverse
     identity
     action
     base-point)
  (implies
   (and
    (q288465-group-p
     group-carrier multiplication inverse identity)
    (q288465-action-p
     group-carrier
     point-carrier
     multiplication
     identity
     action)
   (q288465-member-p point-carrier base-point))
   (q288465-canonical-orbit-quotient-equivalence-p
    group-carrier
    point-carrier
    multiplication
    inverse
    action
    base-point)))

(value-triple :itpeval-statement-checked)
:q
