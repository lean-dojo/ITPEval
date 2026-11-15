;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc:
;; the verification condition for enumerating valid finite red-and-black tile
;; colorings through length 50 by nested loop invariants. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Proper lists over the two constructors are an exact representation of the
;; Why3 sequence type instantiated at color.

(defun ct-enum-color-p (value)
  (or (equal value :red)
      (equal value :black)))

(defun ct-enum-coloring-p (coloring)
  (if (consp coloring)
      (and (ct-enum-color-p (car coloring))
           (ct-enum-coloring-p (cdr coloring)))
    (equal coloring nil)))

(defun ct-enum-repeat-color (count color)
  (declare (xargs :measure (nfix count)))
  (if (and (natp count)
           (< 0 count))
      (cons color
            (ct-enum-repeat-color (- count 1) color))
    nil))

;; Array reads retain the mathematical integer index. Out-of-bounds entries
;; use the Array.make default, so negative indices are not collapsed onto zero.

(defun ct-enum-array-read (array index default)
  (if (and (integerp index)
           (<= 0 index)
           (< index (len array)))
      (nth index array)
    default))

(defun ct-enum-array-set (array index value)
  (declare (xargs :measure (acl2-count array)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons (car array)
                (ct-enum-array-set
                 (cdr array) (- index 1) value)))
      nil)))

(defun ct-enum-array-index-p (array index)
  (and (integerp index)
       (<= 0 index)
       (< index (len array))))

(defun-sk ct-enum-array-update-pointwise-p
    (array index value default)
  (forall (query)
    (implies
     (integerp query)
     (equal
      (ct-enum-array-read
       (ct-enum-array-set array index value)
       query
       default)
      (if (equal query index)
          value
        (ct-enum-array-read array query default))))))

(defun ct-enum-array-update-law-p
    (array index value default)
  (and
   (equal
    (len (ct-enum-array-set array index value))
    (len array))
   (ct-enum-array-update-pointwise-p
    array index value default)))

;; Duplicate-free proper lists represent finite sets extensionally. Every set
;; operation below preserves membership and cardinality independently of list
;; order.

(defun ct-enum-coloring-set-elements-p (set)
  (if (consp set)
      (and (ct-enum-coloring-p (car set))
           (ct-enum-coloring-set-elements-p (cdr set)))
    (equal set nil)))

(defun ct-enum-coloring-set-p (set)
  (and (true-listp set)
       (no-duplicatesp-equal set)
       (ct-enum-coloring-set-elements-p set)))

(defun ct-enum-set-insert (value set)
  (if (member-equal value set)
      set
    (cons value set)))

(defun ct-enum-set-union (left right)
  (if (consp left)
      (ct-enum-set-union
       (cdr left)
       (ct-enum-set-insert (car left) right))
    right))

(defun ct-enum-disjoint-p (left right)
  (if (consp left)
      (and (not (member-equal (car left) right))
           (ct-enum-disjoint-p (cdr left) right))
    t))

(defun ct-enum-count-array-p (array)
  (if (consp array)
      (and (integerp (car array))
           (ct-enum-count-array-p (cdr array)))
    (equal array nil)))

(defun ct-enum-sets-array-p (array)
  (if (consp array)
      (and (ct-enum-coloring-set-p (car array))
           (ct-enum-sets-array-p (cdr array)))
    (equal array nil)))

(defun ct-enum-all-zero-p (array)
  (if (consp array)
      (and (equal (car array) 0)
           (ct-enum-all-zero-p (cdr array)))
    (equal array nil)))

(defun ct-enum-all-empty-sets-p (array)
  (if (consp array)
      (and (equal (car array) nil)
           (ct-enum-all-empty-sets-p (cdr array)))
    (equal array nil)))

(defun ct-enum-initial-count-array-p (array)
  (and (ct-enum-count-array-p array)
       (equal (len array) 51)
       (ct-enum-all-zero-p array)))

(defun ct-enum-initial-sets-array-p (array)
  (and (ct-enum-sets-array-p array)
       (equal (len array) 51)
       (ct-enum-all-empty-sets-p array)))

;; These are the source definitions of the local coloring predicates.

(defun ct-enum-two-red-neighbors-p (coloring index)
  (or
   (and
    (equal
     (ct-enum-array-read coloring (- index 2) :black)
     :red)
    (equal
     (ct-enum-array-read coloring (- index 1) :black)
     :red)
    (<= 2 index))
   (and
    (equal
     (ct-enum-array-read coloring (- index 1) :black)
     :red)
    (equal
     (ct-enum-array-read coloring (+ index 1) :black)
     :red)
    (<= 1 index)
    (<= index (- (len coloring) 2)))
   (and
    (equal
     (ct-enum-array-read coloring (+ index 1) :black)
     :red)
    (equal
     (ct-enum-array-read coloring (+ index 2) :black)
     :red)
    (<= index (- (len coloring) 3)))))

(defun-sk ct-enum-valid-p (coloring)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (len coloring))
      (equal
       (ct-enum-array-read coloring index :black)
       :red))
     (ct-enum-two-red-neighbors-p coloring index))))

(defun ct-enum-first-black-tile (coloring)
  (if (consp coloring)
      (if (equal (car coloring) :black)
          0
        (+ 1
           (ct-enum-first-black-tile (cdr coloring))))
    0))

(defun ct-enum-addleft (red-count coloring)
  (append
   (ct-enum-repeat-color
    (if (and (integerp red-count)
             (< 0 red-count))
        red-count
      0)
    :red)
   (cons :black coloring)))

(defun ct-enum-mapaddleft (set red-count)
  (if (consp set)
      (ct-enum-set-insert
       (ct-enum-addleft red-count (car set))
       (ct-enum-mapaddleft (cdr set) red-count))
    nil))

(defun ct-enum-colorings0 ()
  (list (ct-enum-repeat-color 0 :black)))

(defun ct-enum-colorings1 ()
  (list (ct-enum-repeat-color 1 :black)))

(defun ct-enum-colorings2 ()
  (list (ct-enum-repeat-color 2 :black)))

(defun ct-enum-colorings3 ()
  (list (ct-enum-repeat-color 3 :red)
        (ct-enum-repeat-color 3 :black)))

;; The three predicates below are the outer-loop invariants, with every Why3
;; typed quantifier represented by an ACL2 quantifier plus its domain test.

(defun-sk ct-enum-valid-colorings-present-p (sets bound)
  (forall (coloring index)
    (implies
     (and
      (ct-enum-coloring-p coloring)
      (integerp index)
      (<= 0 index)
      (< index bound)
      (equal (len coloring) index)
      (ct-enum-valid-p coloring))
     (member-equal
      coloring
      (ct-enum-array-read sets index nil)))))

(defun-sk ct-enum-present-colorings-valid-p (sets bound)
  (forall (coloring index)
    (implies
     (and
      (ct-enum-coloring-p coloring)
      (integerp index)
      (<= 0 index)
      (< index bound)
      (member-equal
       coloring
       (ct-enum-array-read sets index nil)))
     (and
      (equal (len coloring) index)
      (ct-enum-valid-p coloring)))))

(defun-sk ct-enum-counts-match-cardinalities-p
    (sets count bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (equal
      (ct-enum-array-read count index 0)
      (len (ct-enum-array-read sets index nil))))))

(defun ct-enum-outer-invariant-p (sets count bound)
  (and
   (ct-enum-valid-colorings-present-p sets bound)
   (ct-enum-present-colorings-valid-p sets bound)
   (ct-enum-counts-match-cardinalities-p
    sets count bound)))

(defun-sk ct-enum-current-set-characterization-p
    (sets n first-black-bound)
  (forall (coloring)
    (implies
     (ct-enum-coloring-p coloring)
     (iff
      (member-equal
       coloring
       (ct-enum-array-read sets n nil))
      (and
       (equal (len coloring) n)
       (ct-enum-valid-p coloring)
       (<
        (ct-enum-first-black-tile coloring)
        first-black-bound))))))

(defun ct-enum-inner-invariant-p
    (sets count n first-black-bound)
  (and
   (ct-enum-outer-invariant-p sets count n)
   (ct-enum-current-set-characterization-p
    sets n first-black-bound)
   (equal
    (ct-enum-array-read count n 0)
    (len (ct-enum-array-read sets n nil)))))

;; This is the final postcondition of enum.

(defun-sk ct-enum-post-characterization-p (sets)
  (forall (index coloring)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (<= index 50)
      (ct-enum-coloring-p coloring)
      (equal (len coloring) index))
     (iff
      (ct-enum-valid-p coloring)
      (member-equal
       coloring
       (ct-enum-array-read sets index nil))))))

(defun ct-enum-postcondition-p (sets count)
  (and
   (equal (len count) 51)
   (equal 51 (len sets))
   (ct-enum-post-characterization-p sets)
   (ct-enum-counts-match-cardinalities-p
    sets count 50)))

;; The source Seq.create side condition used before adding the all-red
;; coloring is retained as a quantified statement.

(defun-sk ct-enum-all-red-through-p (coloring bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (equal
      (ct-enum-array-read coloring index :black)
      :red))))

;; LAST-ADD-VC is the weakest-precondition branch that adds the unique
;; all-red coloring after the inner loop.

(defun ct-enum-last-add-vc-p (sets count n)
  (let* ((red-coloring
          (ct-enum-repeat-color n :red))
         (singleton-red
          (list red-coloring)))
    (and
     (<= 0 n)
     (implies
      (and
       (equal (len red-coloring) n)
       (ct-enum-all-red-through-p red-coloring n))
      (and
       (ct-enum-array-index-p count n)
       (let* ((new-count
               (+ (ct-enum-array-read count n 0) 1))
              (count-next
               (ct-enum-array-set count n new-count)))
         (and
          (ct-enum-array-index-p count n)
          (implies
           (ct-enum-array-update-law-p
            count n new-count 0)
           (and
            (ct-enum-array-index-p sets n)
            (let* ((old-set
                    (ct-enum-array-read sets n nil))
                   (joined-set
                    (ct-enum-set-union
                     old-set singleton-red)))
              (and
               (ct-enum-disjoint-p old-set singleton-red)
               (implies
                (equal
                 (len joined-set)
                 (+ (len old-set)
                    (len singleton-red)))
                (and
                 (ct-enum-array-index-p sets n)
                 (implies
                  (ct-enum-array-update-law-p
                   sets n joined-set nil)
                  (ct-enum-outer-invariant-p
                   (ct-enum-array-set sets n joined-set)
                   count-next
                   (+ n 1))))))))))))))))

;; One inner-loop iteration adds all valid colorings whose first black tile is
;; exactly k and advances the strict first-black bound from k to k+1.

(defun ct-enum-inner-body-vc-p (sets count n k)
  (let* ((source-index (- (- n k) 1))
         (new-count
          (+ (ct-enum-array-read count n 0)
             (ct-enum-array-read count source-index 0)))
         (count-next
          (ct-enum-array-set count n new-count))
         (new-colorings
          (ct-enum-mapaddleft
           (ct-enum-array-read sets source-index nil)
           k))
         (old-set
          (ct-enum-array-read sets n nil))
         (joined-set
          (ct-enum-set-union old-set new-colorings))
         (sets-next
          (ct-enum-array-set sets n joined-set)))
    (and
     (ct-enum-array-index-p count source-index)
     (ct-enum-array-index-p count n)
     (ct-enum-array-index-p count n)
     (implies
      (ct-enum-array-update-law-p
       count n new-count 0)
      (and
       (ct-enum-array-index-p sets source-index)
       (ct-enum-array-index-p sets n)
       (ct-enum-disjoint-p old-set new-colorings)
       (implies
        (equal
         (len joined-set)
         (+ (len old-set)
            (len new-colorings)))
        (and
         (ct-enum-array-index-p sets n)
         (implies
          (ct-enum-array-update-law-p
           sets n joined-set nil)
          (ct-enum-inner-invariant-p
           sets-next count-next n (+ k 1))))))))))

(defun-sk ct-enum-inner-iterations-vc-p
    (sets count n last-k)
  (forall (k)
    (implies
     (and
      (integerp k)
      (<= 3 k)
      (<= k last-k)
      (ct-enum-inner-invariant-p sets count n k))
     (ct-enum-inner-body-vc-p sets count n k))))

(defun-sk ct-enum-inner-loop-vc-p
    (base-sets base-count n last-k)
  (forall (sets count)
    (implies
     (and
      (ct-enum-sets-array-p sets)
      (ct-enum-count-array-p count)
      (equal (len sets) (len base-sets))
      (equal (len count) (len base-count)))
     (and
      (ct-enum-inner-iterations-vc-p
       sets count n last-k)
      (implies
       (ct-enum-inner-invariant-p
        sets count n (+ last-k 1))
       (ct-enum-last-add-vc-p sets count n))))))

;; One outer-loop iteration first installs the first-black-zero colorings,
;; then checks the nonempty and empty inner-loop branches separately.

(defun ct-enum-outer-body-vc-p (sets count n)
  (let* ((previous (- n 1))
         (copied-count
          (ct-enum-array-read count previous 0))
         (count-next
          (ct-enum-array-set count n copied-count))
         (first-black-zero-set
          (ct-enum-mapaddleft
           (ct-enum-array-read sets previous nil)
           0))
         (sets-next
          (ct-enum-array-set
           sets n first-black-zero-set))
         (last-k (- n 1)))
    (and
     (ct-enum-array-index-p count previous)
     (ct-enum-array-index-p count n)
     (implies
      (ct-enum-array-update-law-p
       count n copied-count 0)
      (and
       (ct-enum-array-index-p sets previous)
       (ct-enum-array-index-p sets n)
       (implies
        (ct-enum-array-update-law-p
         sets n first-black-zero-set nil)
        (and
         (implies
          (<= 3 (+ last-k 1))
          (and
           (ct-enum-inner-invariant-p
            sets-next count-next n 3)
           (ct-enum-inner-loop-vc-p
            sets-next count-next n last-k)))
         (implies
          (< (+ last-k 1) 3)
          (ct-enum-last-add-vc-p
           sets-next count-next n)))))))))

(defun-sk ct-enum-outer-iterations-vc-p (sets count)
  (forall (n)
    (implies
     (and
      (integerp n)
      (<= 4 n)
      (<= n 50)
      (ct-enum-outer-invariant-p sets count n))
     (ct-enum-outer-body-vc-p sets count n))))

(defun-sk ct-enum-outer-loop-vc-p
    (base-sets base-count)
  (forall (sets count)
    (implies
     (and
      (ct-enum-sets-array-p sets)
      (ct-enum-count-array-p count)
      (equal (len sets) (len base-sets))
      (equal (len count) (len base-count)))
     (and
      (ct-enum-outer-iterations-vc-p sets count)
      (implies
       (ct-enum-outer-invariant-p sets count 51)
       (ct-enum-postcondition-p sets count))))))

;; This nests the eight initialization assignments with the exact array
;; bounds and extensional update laws appearing in the exported VC.

(defun ct-enum-initialization-vc-p (count sets)
  (and
   (ct-enum-array-index-p count 0)
   (implies
    (ct-enum-array-update-law-p count 0 1 0)
    (let* ((count0 (ct-enum-array-set count 0 1))
           (set0 (ct-enum-colorings0)))
      (and
       (ct-enum-array-index-p sets 0)
       (implies
        (ct-enum-array-update-law-p sets 0 set0 nil)
        (let* ((sets0 (ct-enum-array-set sets 0 set0)))
          (and
           (ct-enum-array-index-p count0 1)
           (implies
            (ct-enum-array-update-law-p count0 1 1 0)
            (let* ((count1 (ct-enum-array-set count0 1 1))
                   (set1 (ct-enum-colorings1)))
              (and
               (ct-enum-array-index-p sets0 1)
               (implies
                (ct-enum-array-update-law-p sets0 1 set1 nil)
                (let* ((sets1
                        (ct-enum-array-set sets0 1 set1)))
                  (and
                   (ct-enum-array-index-p count1 2)
                   (implies
                    (ct-enum-array-update-law-p count1 2 1 0)
                    (let* ((count2
                            (ct-enum-array-set count1 2 1))
                           (set2 (ct-enum-colorings2)))
                      (and
                       (ct-enum-array-index-p sets1 2)
                       (implies
                        (ct-enum-array-update-law-p
                         sets1 2 set2 nil)
                        (let* ((sets2
                                (ct-enum-array-set
                                 sets1 2 set2)))
                          (and
                           (ct-enum-array-index-p count2 3)
                           (implies
                            (ct-enum-array-update-law-p
                             count2 3 2 0)
                            (let* ((count3
                                    (ct-enum-array-set
                                     count2 3 2))
                                   (set3
                                    (ct-enum-colorings3)))
                              (and
                               (ct-enum-array-index-p sets2 3)
                               (implies
                                (ct-enum-array-update-law-p
                                 sets2 3 set3 nil)
                                (let* ((sets3
                                        (ct-enum-array-set
                                         sets2 3 set3)))
                                  (and
                                   (implies
                                    (<= 4 (+ 50 1))
                                    (and
                                     (ct-enum-outer-invariant-p
                                      sets3 count3 4)
                                     (ct-enum-outer-loop-vc-p
                                      sets3 count3)))
                                   (implies
                                    (< (+ 50 1) 4)
                                    (ct-enum-postcondition-p
                                     sets3 count3))))))))))))))))))))))))))))

(defun-sk ct-enum-all-initial-sets-vc-p (count)
  (forall (sets)
    (implies
     (ct-enum-initial-sets-array-p sets)
     (ct-enum-initialization-vc-p count sets))))

(defun-sk ct-enum-all-initial-counts-vc-p ()
  (forall (count)
    (implies
     (ct-enum-initial-count-array-p count)
     (and
      (<= 0 51)
      (ct-enum-all-initial-sets-vc-p count)))))

(defun
    ntp4vc-colored-tiles-enumqtvc-statement
    ()
  (and
   (<= 0 51)
   (ct-enum-all-initial-counts-vc-p)))

(value-triple :itpeval-statement-checked)
:q
