;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/koda_ruskey_KodaRuskey_mainqtvc: the Koda-Ruskey forest-coloring
;; main verification condition, initializing an all-white forest and requiring
;; a complete, valid, pairwise-distinct stored enumeration. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Colors and forests are exact encodings of the two source inductive types.

(defun kr-color-p (color)
  (or (equal color :kr-white)
      (equal color :kr-black)))

(defun kr-e ()
  :kr-e)

(defun kr-n (index left right)
  (list :kr-n index left right))

(defun kr-n-shape-p (forest)
  (and
   (true-listp forest)
   (equal (len forest) 4)
   (equal (car forest) :kr-n)))

(defun kr-forest-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      t
    (and
     (kr-n-shape-p forest)
     (integerp (cadr forest))
     (kr-forest-p (caddr forest))
     (kr-forest-p (cadddr forest)))))

(defun kr-n-index (forest)
  (cadr forest))

(defun kr-n-left (forest)
  (caddr forest))

(defun kr-n-right (forest)
  (cadddr forest))

(defun kr-color-list-p (colors)
  (if (consp colors)
      (and
       (kr-color-p (car colors))
       (kr-color-list-p (cdr colors)))
    (equal colors nil)))

;; A handle denotes an arbitrary total function from integers to colors.
;; KR-COLORING-RAW is a conservative generic operation symbol. List-derived
;; colorings are represented separately so their application is definitional.

(defstub kr-coloring-raw (handle index) t)
(defstub kr-default-color-raw () t)

(defun kr-normalize-color (value)
  (if (equal value :kr-black)
      :kr-black
    :kr-white))

(defun kr-default-color ()
  (kr-normalize-color (kr-default-color-raw)))

(defun kr-int-to-nat (index)
  (if (and
       (integerp index)
       (< 0 index))
      index
    0))

(defun kr-nth-color-nat (colors index)
  (if (and
       (natp index)
       (< index (len colors)))
      (nth index colors)
    (kr-default-color)))

(defun kr-nth-color-int (colors index)
  (kr-nth-color-nat colors (kr-int-to-nat index)))

(defun kr-list-coloring (colors)
  (list :kr-list-coloring colors))

(defun kr-handle-coloring (handle)
  (list :kr-handle-coloring handle))

(defun kr-list-coloring-shape-p (coloring)
  (and
   (true-listp coloring)
   (equal (len coloring) 2)
   (equal (car coloring) :kr-list-coloring)))

(defun kr-handle-coloring-shape-p (coloring)
  (and
   (true-listp coloring)
   (equal (len coloring) 2)
   (equal (car coloring) :kr-handle-coloring)))

(defun kr-coloring-p (coloring)
  (or
   (and
    (kr-list-coloring-shape-p coloring)
    (kr-color-list-p (cadr coloring)))
   (kr-handle-coloring-shape-p coloring)))

(defun kr-coloring-list-p (colorings)
  (if (consp colorings)
      (and
       (kr-coloring-p (car colorings))
       (kr-coloring-list-p (cdr colorings)))
    (equal colorings nil)))

(defun kr-coloring-apply (coloring index)
  (if (kr-list-coloring-shape-p coloring)
      (kr-nth-color-int (cadr coloring) index)
    (if (kr-handle-coloring-shape-p coloring)
        (kr-normalize-color
         (kr-coloring-raw (cadr coloring) index))
      (kr-default-color))))

;; Forest specifications.

(defun kr-size-forest (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      0
    (if (kr-n-shape-p forest)
        (+
         1
         (kr-size-forest (kr-n-left forest))
         (kr-size-forest (kr-n-right forest)))
      0)))

(defun kr-mem-forest-p (number forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      nil
    (and
     (kr-n-shape-p forest)
     (or
      (equal (kr-n-index forest) number)
      (kr-mem-forest-p number (kr-n-left forest))
      (kr-mem-forest-p number (kr-n-right forest))))))

(defun-sk kr-between-range-forest-p (lower upper forest)
  (forall (number)
    (implies
     (integerp number)
     (implies
      (kr-mem-forest-p number forest)
      (and
       (<= lower number)
       (< number upper))))))

(defun-sk kr-disjoint-forests-p (left right)
  (forall (number)
    (implies
     (integerp number)
     (implies
      (kr-mem-forest-p number left)
      (not
       (kr-mem-forest-p number right))))))

(defun kr-no-repeated-forest-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      t
    (and
     (kr-n-shape-p forest)
     (kr-no-repeated-forest-p (kr-n-left forest))
     (kr-no-repeated-forest-p (kr-n-right forest))
     (not
      (kr-mem-forest-p
       (kr-n-index forest)
       (kr-n-left forest)))
     (not
      (kr-mem-forest-p
       (kr-n-index forest)
       (kr-n-right forest)))
     (kr-disjoint-forests-p
      (kr-n-left forest)
      (kr-n-right forest)))))

(defun kr-valid-nums-forest-p (forest bound)
  (and
   (kr-between-range-forest-p 0 bound forest)
   (kr-no-repeated-forest-p forest)))

(defun kr-white-forest-p (forest coloring)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      t
    (and
     (kr-n-shape-p forest)
     (equal
      (kr-coloring-apply
       coloring
       (kr-n-index forest))
      :kr-white)
     (kr-white-forest-p
      (kr-n-left forest)
      coloring)
     (kr-white-forest-p
      (kr-n-right forest)
      coloring))))

(defun kr-valid-coloring-p (forest coloring)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      t
    (and
     (kr-n-shape-p forest)
     (kr-valid-coloring-p
      (kr-n-right forest)
      coloring)
     (if (equal
          (kr-coloring-apply
           coloring
           (kr-n-index forest))
          :kr-white)
         (kr-white-forest-p
          (kr-n-left forest)
          coloring)
       (kr-valid-coloring-p
        (kr-n-left forest)
        coloring)))))

(defun kr-count-forest (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      1
    (if (kr-n-shape-p forest)
        (*
         (+ 1
            (kr-count-forest
             (kr-n-left forest)))
         (kr-count-forest
          (kr-n-right forest)))
      1)))

(defun-sk kr-eq-coloring-p (bound left right)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound))
      (equal
       (kr-coloring-apply left index)
       (kr-coloring-apply right index))))))

;; Stack and traversal specifications.

(defun kr-mem-stack-p (number stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (or
       (kr-mem-forest-p number (car stack))
       (kr-mem-stack-p number (cdr stack)))
    nil))

(defun kr-even-forest-p (forest)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      nil
    (and
     (kr-n-shape-p forest)
     (or
      (not
       (kr-even-forest-p
        (kr-n-left forest)))
      (kr-even-forest-p
       (kr-n-right forest))))))

(defun kr-final-forest-p (forest coloring)
  (declare (xargs :measure (acl2-count forest)))
  (if (equal forest (kr-e))
      t
    (and
     (kr-n-shape-p forest)
     (equal
      (kr-coloring-apply
       coloring
       (kr-n-index forest))
      :kr-black)
     (kr-final-forest-p
      (kr-n-left forest)
      coloring)
     (if (not
          (kr-even-forest-p
           (kr-n-left forest)))
         (kr-white-forest-p
          (kr-n-right forest)
          coloring)
       (kr-final-forest-p
        (kr-n-right forest)
        coloring)))))

(defun kr-any-forest-p (forest coloring)
  (or
   (kr-white-forest-p forest coloring)
   (kr-final-forest-p forest coloring)))

(defun-sk kr-unchanged-p (stack left right)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (kr-mem-stack-p index stack)
      (equal
       (kr-coloring-apply left index)
       (kr-coloring-apply right index))))))

(defun kr-inverse-p (stack left right)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (and
       (or
        (and
         (kr-white-forest-p (car stack) left)
         (kr-final-forest-p (car stack) right))
        (and
         (kr-final-forest-p (car stack) left)
         (kr-white-forest-p (car stack) right)))
       (if (kr-even-forest-p (car stack))
           (kr-unchanged-p (cdr stack) left right)
         (kr-inverse-p (cdr stack) left right)))
    t))

(defun kr-any-stack-p (stack coloring)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (and
       (kr-any-forest-p (car stack) coloring)
       (kr-any-stack-p (cdr stack) coloring))
    t))

(defun kr-last-forest (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (and
       (consp stack)
       (consp (cdr stack)))
      (kr-last-forest (cdr stack))
    (car stack)))

(defun kr-drop-last-forest (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (and
       (consp stack)
       (consp (cdr stack)))
      (cons
       (car stack)
       (kr-drop-last-forest (cdr stack)))
    nil))

;; This recursion is equivalent to the three constructors of the source SUB
;; relation: reflexivity, descent to a right child, and black-node append.

(defun kr-sub-p (stack forest coloring)
  (declare (xargs :measure (acl2-count forest)))
  (or
   (equal stack (list forest))
   (and
    (kr-n-shape-p forest)
    (or
     (kr-sub-p
      stack
      (kr-n-right forest)
      coloring)
     (and
      (consp stack)
      (equal
       (kr-last-forest stack)
       (kr-n-right forest))
      (kr-sub-p
       (kr-drop-last-forest stack)
       (kr-n-left forest)
       coloring)
      (equal
       (kr-coloring-apply
        coloring
        (kr-n-index forest))
       :kr-black))))))

(defun kr-count-stack (stack)
  (declare (xargs :measure (acl2-count stack)))
  (if (consp stack)
      (*
       (kr-count-forest (car stack))
       (kr-count-stack (cdr stack)))
    1))

;; STORED-SOLUTIONS preserves the source's three quantified clauses.

(defun-sk kr-stored-old-entries-p
    (bound first second start)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index start))
      (kr-eq-coloring-p
       bound
       (nth (kr-int-to-nat index) second)
       (nth (kr-int-to-nat index) first))))))

(defun-sk kr-stored-outside-stack-p
    (bound coloring stack solution)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index bound)
       (not
        (kr-mem-stack-p index stack)))
      (equal
       (kr-coloring-apply solution index)
       (kr-coloring-apply coloring index))))))

(defun-sk kr-stored-distinct-from-p
    (bound solutions start stop index)
  (forall (other)
    (implies
     (integerp other)
     (implies
      (and
       (<= start other)
       (< other stop)
       (not (equal index other)))
      (not
       (kr-eq-coloring-p
        bound
        (nth (kr-int-to-nat index) solutions)
        (nth (kr-int-to-nat other) solutions)))))))

(defun kr-stored-new-entry-p
    (forest coloring stack solutions start stop index)
  (let ((bound (kr-size-forest forest))
        (solution
         (nth (kr-int-to-nat index) solutions)))
    (and
     (kr-valid-coloring-p forest solution)
     (kr-stored-outside-stack-p
      bound coloring stack solution)
     (kr-stored-distinct-from-p
      bound solutions start stop index))))

(defun-sk kr-stored-new-entries-p
    (forest coloring stack solutions start stop)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= start index)
       (< index stop))
      (kr-stored-new-entry-p
       forest coloring stack solutions
       start stop index)))))

(defun kr-stored-solutions-p
    (forest coloring stack first second)
  (let ((start (len first))
        (stop (len second))
        (bound (kr-size-forest forest)))
    (and
     (equal
      (- stop start)
      (kr-count-stack stack))
     (kr-stored-old-entries-p
      bound first second start)
     (kr-stored-new-entries-p
      forest coloring stack second start stop))))

;; The universally quantified result obligation of MAIN.

(defun-sk kr-bits-agree-outside-stack-p
    (left right stack)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (not
       (kr-mem-stack-p index stack))
      (equal
       (kr-nth-color-int left index)
       (kr-nth-color-int right index))))))

(defun-sk kr-main-distinct-from-p
    (bound visited index)
  (forall (other)
    (implies
     (integerp other)
     (implies
      (and
       (<= 0 other)
       (< other (len visited))
       (not (equal index other)))
      (not
       (kr-eq-coloring-p
        bound
        (nth (kr-int-to-nat index) visited)
        (nth (kr-int-to-nat other) visited)))))))

(defun kr-main-visited-entry-p
    (forest bound visited index)
  (and
   (kr-valid-coloring-p
    forest
    (nth (kr-int-to-nat index) visited))
   (kr-main-distinct-from-p
    bound visited index)))

(defun-sk kr-main-all-visited-p
    (forest bound visited)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len visited)))
      (kr-main-visited-entry-p
       forest bound visited index)))))

(defun kr-main-result-premises-p
    (forest bits bits1 visited)
  (let ((stack (list forest)))
    (and
     (kr-bits-agree-outside-stack-p
      bits1 bits stack)
     (kr-inverse-p
      stack
      (kr-list-coloring bits)
      (kr-list-coloring bits1))
     (kr-valid-coloring-p
      forest
      (kr-list-coloring bits1))
     (kr-stored-solutions-p
      forest
      (kr-list-coloring bits1)
      stack nil visited))))

(defun kr-main-result-postcondition-p
    (forest bits1 visited)
  (and
   (equal
    (len visited)
    (kr-count-forest forest))
   (kr-main-all-visited-p
    forest
    (len bits1)
    visited)))

(defun-sk kr-main-all-results-p (forest bits)
  (forall (bits1 visited)
    (implies
     (and
      (kr-color-list-p bits1)
      (kr-coloring-list-p visited))
     (implies
      (equal
       (len bits1)
       (len bits))
      (implies
       (kr-main-result-premises-p
        forest bits bits1 visited)
       (kr-main-result-postcondition-p
        forest bits1 visited))))))

(defun kr-main-conclusion-p (forest bits)
  (let ((stack (list forest))
        (coloring (kr-list-coloring bits)))
    (and
     (equal
      (kr-size-forest forest)
      (len bits))
     (kr-valid-nums-forest-p
      forest
      (len bits))
     (kr-sub-p stack forest coloring)
     (kr-any-stack-p stack coloring)
     (kr-valid-coloring-p forest coloring)
     (kr-main-all-results-p forest bits))))

(defun
  ntp4vc-pearl-koda-ruskey-kodaruskey-mainqtvc-statement
  (forest bits)
  (implies
   (and
    (kr-forest-p forest)
    (kr-color-list-p bits)
    (kr-white-forest-p
     forest
     (kr-list-coloring bits))
    (equal
     (kr-size-forest forest)
     (len bits))
    (kr-valid-nums-forest-p
     forest
     (len bits)))
   (kr-main-conclusion-p forest bits)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
