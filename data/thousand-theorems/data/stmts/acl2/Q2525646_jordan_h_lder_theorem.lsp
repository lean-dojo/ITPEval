;; Statement-only formalization of thousand-theorems corpus artifact Q2525646,
;; "Jordan–Hölder theorem": in any Jordan-Holder lattice, two finite nonempty
;; composition series with the same head and last element have their successive
;; factors matched bijectively by the lattice's pair-isomorphism relation. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The carrier, meet, join, maximality relation, and pair-isomorphism relation
;; are arbitrary tame APPLY$ function objects. FN-EQUAL supplies unbounded
;; universal quantification over the ACL2 universe. Equational lattice laws are
;; bidirectionally equivalent to the source Lattice structure, with x <= y
;; represented by meet(x,y)=x. A composition series is intrinsically finite, so
;; a nonempty list is exactly its finite-indexed family of lattice elements.
;; Enumerating every permutation of its factor indices is exactly the internal
;; existential bijection in CompositionSeries.Equivalent.

(defun q2525646-quoted (object)
  (list 'quote object))

(defun q2525646-term-list (terms)
  (if (consp terms)
      (list
       'cons
       (car terms)
       (q2525646-term-list (cdr terms)))
    (q2525646-quoted nil)))

(defun q2525646-static-apply-term (function arguments)
  (list
   'apply$
   (q2525646-quoted function)
   (q2525646-term-list arguments)))

(defun q2525646-static-predicate-term (function arguments)
  (list
   'if
   (q2525646-static-apply-term function arguments)
   (q2525646-quoted t)
   (q2525646-quoted nil)))

(defun q2525646-and-terms (terms)
  (if (consp terms)
      (list
       'if
       (car terms)
       (q2525646-and-terms (cdr terms))
       (q2525646-quoted nil))
    (q2525646-quoted t)))

(defun q2525646-not-term (term)
  (list
   'if
   term
   (q2525646-quoted nil)
   (q2525646-quoted t)))

(defun q2525646-implies-term (hypothesis conclusion)
  (list
   'if
   hypothesis
   conclusion
   (q2525646-quoted t)))

(defun q2525646-true-function (formals)
  (list 'lambda formals (q2525646-quoted t)))

(defun q2525646-universal-p (function formals)
  (let ((always-true (q2525646-true-function formals)))
    (and
     (tamep-functionp function)
     (tamep-functionp always-true)
     (fn-equal function always-true))))

(defun q2525646-member-p (carrier object)
  (if (apply$ carrier (list object)) t nil))

(defun q2525646-binary-p (relation left right)
  (if (apply$ relation (list left right)) t nil))

(defun q2525646-binary-value (operation left right)
  (apply$ operation (list left right)))

;; Equational presentation of an arbitrary lattice.

(defun q2525646-lattice-laws-function (carrier meet join)
  (let* ((x-in
          (q2525646-static-predicate-term carrier '(x)))
         (y-in
          (q2525646-static-predicate-term carrier '(y)))
         (z-in
          (q2525646-static-predicate-term carrier '(z)))
         (meet-xx
          (q2525646-static-apply-term meet '(x x)))
         (join-xx
          (q2525646-static-apply-term join '(x x)))
         (meet-xy
          (q2525646-static-apply-term meet '(x y)))
         (join-xy
          (q2525646-static-apply-term join '(x y)))
         (meet-yx
          (q2525646-static-apply-term meet '(y x)))
         (join-yx
          (q2525646-static-apply-term join '(y x)))
         (meet-yz
          (q2525646-static-apply-term meet '(y z)))
         (join-yz
          (q2525646-static-apply-term join '(y z))))
    (list
     'lambda
     '(x y z)
     (q2525646-and-terms
      (list
       (q2525646-implies-term
        x-in
        (q2525646-and-terms
         (list
          (q2525646-static-predicate-term carrier (list meet-xx))
          (q2525646-static-predicate-term carrier (list join-xx))
          (list 'equal meet-xx 'x)
          (list 'equal join-xx 'x))))
       (q2525646-implies-term
        (q2525646-and-terms (list x-in y-in))
        (q2525646-and-terms
         (list
          (q2525646-static-predicate-term carrier (list meet-xy))
          (q2525646-static-predicate-term carrier (list join-xy))
          (list 'equal meet-xy meet-yx)
          (list 'equal join-xy join-yx)
          (list
           'equal
           (q2525646-static-apply-term
            meet
            (list 'x join-xy))
           'x)
          (list
           'equal
           (q2525646-static-apply-term
            join
            (list 'x meet-xy))
           'x))))
       (q2525646-implies-term
        (q2525646-and-terms (list x-in y-in z-in))
        (q2525646-and-terms
         (list
          (list
           'equal
           (q2525646-static-apply-term meet (list meet-xy 'z))
           (q2525646-static-apply-term meet (list 'x meet-yz)))
          (list
           'equal
           (q2525646-static-apply-term join (list join-xy 'z))
           (q2525646-static-apply-term join (list 'x join-yz)))))))))))

(defun q2525646-lattice-p (carrier meet join)
  (and
   (tamep-functionp carrier)
   (tamep-functionp meet)
   (tamep-functionp join)
   (q2525646-universal-p
    (q2525646-lattice-laws-function carrier meet join)
    '(x y z))))

;; The IsMaximal axioms and second-isomorphism axiom from
;; JordanHolderLattice.

(defun q2525646-jh-max-laws-function
    (carrier meet join maximal iso)
  (let* ((x-in
          (q2525646-static-predicate-term carrier '(x)))
         (y-in
          (q2525646-static-predicate-term carrier '(y)))
         (z-in
          (q2525646-static-predicate-term carrier '(z)))
         (meet-xy
          (q2525646-static-apply-term meet '(x y)))
         (join-xy
          (q2525646-static-apply-term join '(x y)))
         (max-xy
          (q2525646-static-predicate-term maximal '(x y)))
         (max-xz
          (q2525646-static-predicate-term maximal '(x z)))
         (max-yz
          (q2525646-static-predicate-term maximal '(y z)))
         (max-x-join
          (q2525646-static-predicate-term
           maximal
           (list 'x join-xy)))
         (max-y-join
          (q2525646-static-predicate-term
           maximal
           (list 'y join-xy)))
         (pair-x-join
          (list 'cons 'x join-xy))
         (pair-meet-y
          (list 'cons meet-xy 'y)))
    (list
     'lambda
     '(x y z)
     (q2525646-and-terms
      (list
       (q2525646-implies-term
        (q2525646-and-terms (list x-in y-in max-xy))
        (q2525646-and-terms
         (list
          (list 'equal meet-xy 'x)
          (q2525646-not-term (list 'equal 'x 'y)))))
       (q2525646-implies-term
        (q2525646-and-terms
         (list
          x-in
          y-in
          z-in
          max-xz
          max-yz
          (q2525646-not-term (list 'equal 'x 'y))))
        (list 'equal join-xy 'z))
       (q2525646-implies-term
        (q2525646-and-terms
         (list x-in y-in max-x-join max-y-join))
        (q2525646-static-predicate-term
         maximal
         (list meet-xy 'x)))
       (q2525646-implies-term
        (q2525646-and-terms (list x-in y-in max-x-join))
        (q2525646-static-predicate-term
         iso
         (list pair-x-join pair-meet-y))))))))

;; Iso is a symmetric and transitive relation on ordered pairs. ACL2 cons pairs
;; are the direct uncurried presentation of the source X x X arguments.

(defun q2525646-jh-iso-laws-function (carrier iso)
  (let* ((a-in
          (q2525646-static-predicate-term carrier '(a)))
         (b-in
          (q2525646-static-predicate-term carrier '(b)))
         (c-in
          (q2525646-static-predicate-term carrier '(c)))
         (d-in
          (q2525646-static-predicate-term carrier '(d)))
         (e-in
          (q2525646-static-predicate-term carrier '(e)))
         (f-in
          (q2525646-static-predicate-term carrier '(f)))
         (pair-ab (list 'cons 'a 'b))
         (pair-cd (list 'cons 'c 'd))
         (pair-ef (list 'cons 'e 'f))
         (iso-ab-cd
          (q2525646-static-predicate-term
           iso
           (list pair-ab pair-cd)))
         (iso-cd-ef
          (q2525646-static-predicate-term
           iso
           (list pair-cd pair-ef))))
    (list
     'lambda
     '(a b c d e f)
     (q2525646-and-terms
      (list
       (q2525646-implies-term
        (q2525646-and-terms
         (list a-in b-in c-in d-in iso-ab-cd))
        (q2525646-static-predicate-term
         iso
         (list pair-cd pair-ab)))
       (q2525646-implies-term
        (q2525646-and-terms
         (list
          a-in b-in c-in d-in e-in f-in
          iso-ab-cd iso-cd-ef))
        (q2525646-static-predicate-term
         iso
         (list pair-ab pair-ef))))))))

(defun q2525646-jordan-holder-lattice-p
    (carrier meet join maximal iso)
  (and
   (q2525646-lattice-p carrier meet join)
   (tamep-functionp maximal)
   (tamep-functionp iso)
   (q2525646-universal-p
    (q2525646-jh-max-laws-function
     carrier meet join maximal iso)
    '(x y z))
   (q2525646-universal-p
    (q2525646-jh-iso-laws-function carrier iso)
    '(a b c d e f))))

;; Nonempty finite series whose consecutive elements satisfy IsMaximal.

(defun q2525646-series-elements-p (carrier series)
  (if (consp series)
      (and
       (q2525646-member-p carrier (car series))
       (q2525646-series-elements-p carrier (cdr series)))
    t))

(defun q2525646-series-steps-p (maximal series)
  (if (and (consp series) (consp (cdr series)))
      (and
       (q2525646-binary-p
        maximal
        (car series)
        (car (cdr series)))
       (q2525646-series-steps-p maximal (cdr series)))
    t))

(defun q2525646-composition-series-p
    (carrier maximal series)
  (and
   (true-listp series)
   (consp series)
   (q2525646-series-elements-p carrier series)
   (q2525646-series-steps-p maximal series)))

(defun q2525646-series-last (series)
  (car (last series)))

;; Exact finite presentation of the existential equivalence of factor lists.

(defun q2525646-factor-indices-aux (index count)
  (if (zp count)
      nil
    (cons
     index
     (q2525646-factor-indices-aux (+ 1 index) (- count 1)))))

(defun q2525646-factor-indices (series)
  (q2525646-factor-indices-aux 0 (- (len series) 1)))

(defun q2525646-insert-at-splits (item prefix suffix)
  (declare (xargs :measure (len suffix)))
  (if (consp suffix)
      (cons
       (append prefix (cons item suffix))
       (q2525646-insert-at-splits
        item
        (append prefix (list (car suffix)))
        (cdr suffix)))
    (list (append prefix (list item)))))

(defun q2525646-insert-into-permutations (item permutations)
  (if (consp permutations)
      (append
       (q2525646-insert-at-splits
        item nil (car permutations))
       (q2525646-insert-into-permutations
        item (cdr permutations)))
    nil))

(defun q2525646-permutations (items)
  (if (consp items)
      (q2525646-insert-into-permutations
       (car items)
       (q2525646-permutations (cdr items)))
    (list nil)))

(defun q2525646-factor-pairs-iso-p
    (iso source target permutation)
  (if (and (consp (cdr source)) (consp permutation))
      (let ((target-index (car permutation)))
        (and
         (q2525646-binary-p
          iso
          (cons (car source) (car (cdr source)))
          (cons
           (nth target-index target)
           (nth (+ 1 target-index) target)))
         (q2525646-factor-pairs-iso-p
          iso
          (cdr source)
          target
          (cdr permutation))))
    (and
     (not (consp (cdr source)))
     (not (consp permutation)))))

(defun q2525646-some-factor-permutation-p
    (iso source target permutations)
  (if (consp permutations)
      (or
       (q2525646-factor-pairs-iso-p
        iso source target (car permutations))
       (q2525646-some-factor-permutation-p
        iso source target (cdr permutations)))
    nil))

(defun q2525646-equivalent-p (iso source target)
  (and
   (equal (len source) (len target))
   (q2525646-some-factor-permutation-p
    iso
    source
    target
    (q2525646-permutations
     (q2525646-factor-indices source)))))

(defun thousand-theorems-q2525646-jordan-holder-theorem-statement
    (carrier meet join maximal iso series-1 series-2)
  (implies
   (and
    (q2525646-jordan-holder-lattice-p
     carrier meet join maximal iso)
    (q2525646-composition-series-p
     carrier maximal series-1)
    (q2525646-composition-series-p
     carrier maximal series-2)
    (equal (car series-1) (car series-2))
    (equal
     (q2525646-series-last series-1)
     (q2525646-series-last series-2)))
   (q2525646-equivalent-p iso series-1 series-2)))

;; Admission-time tameness audit for every reified universal law.

(defun q2525646-all-reified-functions-tame-p ()
  (let ((unary '(lambda (x) (quote t)))
        (binary '(lambda (x y) x)))
    (and
     (tamep-functionp
      (q2525646-true-function '(x)))
     (tamep-functionp
      (q2525646-lattice-laws-function
       unary binary binary))
     (tamep-functionp
      (q2525646-jh-max-laws-function
       unary binary binary binary binary))
     (tamep-functionp
      (q2525646-jh-iso-laws-function
       unary binary)))))

(value-triple
 (if (q2525646-all-reified-functions-tame-p)
     :itpeval-tame-reified-functions-checked
   (er hard 'q2525646-tameness
       "A reified statement function is not tame.")))

(value-triple :itpeval-statement-checked)
:q
