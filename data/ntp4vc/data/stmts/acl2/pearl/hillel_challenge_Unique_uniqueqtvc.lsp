;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/hillel_challenge_Unique_uniqueqtvc: the verification condition for
;; constructing a duplicate-free list containing exactly the values occurring
;; in an integer list. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 integers and finite true lists directly represent the source integers
;; and lists. Int.toNat maps negative integers to zero, and source integer-list
;; lookup returns the default integer zero outside the list.

(defun uqvc-integer-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (integerp (car xs))
     (uqvc-integer-list-p (cdr xs)))))

(defun uqvc-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun uqvc-nth-int (index xs)
  (let ((value (nth (uqvc-int-to-nat index) xs)))
    (if (integerp value)
        value
      0)))

;; A source finite map from integers to unit is exactly a finite set of integer
;; keys. Strictly increasing integer lists give a canonical, bijective
;; representation, so ACL2 equality is source finite-map equality.

(defun uqvc-map-p (keys)
  (if (endp keys)
      (equal keys nil)
    (and
     (integerp (car keys))
     (uqvc-map-p (cdr keys))
     (or
      (endp (cdr keys))
      (< (car keys) (cadr keys))))))

(defun uqvc-map-insert (key keys)
  (if (endp keys)
      (list key)
    (if (equal key (car keys))
        keys
      (if (< key (car keys))
          (cons key keys)
        (cons
         (car keys)
         (uqvc-map-insert key (cdr keys)))))))

;; This is the source predicate mem: membership among indices 0 <= j < bound,
;; with the existential witness retained internally.

(defun-sk uqvc-mem-p (value xs bound)
  (exists (index)
    (and
     (integerp index)
     (<= 0 index)
     (< index bound)
     (equal (uqvc-nth-int index xs) value))))

(defun-sk uqvc-prefix-map-equivalent-p (a bound keys)
  (forall (value)
    (implies
     (integerp value)
     (iff
      (uqvc-mem-p value a bound)
      (member-equal value keys)))))

(defun-sk uqvc-prefix-list-equivalent-p
    (a a-bound res res-bound)
  (forall (value)
    (implies
     (integerp value)
     (iff
      (uqvc-mem-p value a a-bound)
      (uqvc-mem-p value res res-bound)))))

(defun-sk uqvc-unique-prefix-p (res bound)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (<= 0 left)
      (< left right)
      (< right bound))
     (not
      (equal
       (uqvc-nth-int left res)
       (uqvc-nth-int right res))))))

(defun uqvc-invariant-p (a index keys res length)
  (and
   (<= 0 length)
   (<= length index)
   (uqvc-prefix-map-equivalent-p a index keys)
   (uqvc-prefix-list-equivalent-p a index res length)
   (uqvc-unique-prefix-p res length)))

;; List.set changes the requested natural-number position and leaves the list
;; unchanged when that position is out of range.

(defun uqvc-set-nat (xs index value)
  (declare (xargs :measure (len xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (uqvc-set-nat (cdr xs) (- index 1) value)))))

(defun uqvc-list-set (xs index value)
  (uqvc-set-nat xs (uqvc-int-to-nat index) value))

;; The source equality between integer-indexed lookup functions is represented
;; extensionally, over every mathematical integer argument.

(defun-sk uqvc-update-function-equality-p
    (updated original index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (uqvc-nth-int argument updated)
      (if (equal argument index)
          value
        (uqvc-nth-int argument original))))))

(defun-sk uqvc-zero-initialized-p (res length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index length))
      (equal (uqvc-nth-int index res) 0)))))

(defun-sk uqvc-copied-prefix-p (result source length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index length))
      (equal
       (uqvc-nth-int index result)
       (uqvc-nth-int (+ 0 index) source))))))

(defun uqvc-result-property-p (a result)
  (and
   (uqvc-prefix-list-equivalent-p
    result (len result) a (len a))
   (uqvc-unique-prefix-p result (len result))))

(defun-sk uqvc-all-results-p (a source length)
  (forall (result)
    (implies
     (uqvc-integer-list-p result)
     (implies
      (and
       (equal (len result) length)
       (uqvc-copied-prefix-p result source length))
      (uqvc-result-property-p a result)))))

(defun uqvc-final-exit-p (a o1 keys res length)
  (implies
   (uqvc-invariant-p a (+ o1 1) keys res length)
   (and
    (<= 0 0)
    (<= 0 length)
    (<= (+ 0 length) (len res))
    (uqvc-all-results-p a res length))))

(defun-sk uqvc-all-inserted-maps-p
    (a res keys res1 length index)
  (forall (keys2)
    (implies
     (uqvc-map-p keys2)
     (implies
      (equal
       keys2
       (uqvc-map-insert
        (uqvc-nth-int index a)
        keys))
      (and
       (<= 0 index)
       (< index (len a))
       (let*
           ((value (uqvc-nth-int index a))
            (updated
             (uqvc-list-set res1 length value)))
         (and
          (<= 0 length)
          (< length (len res1))
          (implies
           (equal (len updated) (len res1))
           (implies
            (uqvc-update-function-equality-p
             updated res1 length value)
            (uqvc-invariant-p
             a
             (+ index 1)
             keys2
             updated
             (+ length 1)))))))))))

(defun uqvc-loop-step-p (a res keys res1 length index)
  (and
   (<= 0 index)
   (< index (len a))
   (if
       (not
        (member-equal
         (uqvc-nth-int index a)
         keys))
       (and
        (<= 0 index)
        (< index (len a))
        (uqvc-all-inserted-maps-p
         a res keys res1 length index))
     (uqvc-invariant-p
      a
      (+ index 1)
      keys
      res1
      length))))

(defun-sk uqvc-all-loop-steps-p
    (a o1 res keys res1 length)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (<= index o1)
       (uqvc-invariant-p
        a index keys res1 length))
      (uqvc-loop-step-p
       a res keys res1 length index)))))

(defun uqvc-state-obligations-p
    (a o1 res keys res1 length)
  (and
   (uqvc-all-loop-steps-p
    a o1 res keys res1 length)
   (uqvc-final-exit-p
    a o1 keys res1 length)))

(defun-sk uqvc-all-loop-states-p (a o1 res)
  (forall (length res1 keys)
    (implies
     (and
      (integerp length)
      (uqvc-integer-list-p res1)
      (uqvc-map-p keys))
     (implies
      (equal (len res1) (len res))
      (uqvc-state-obligations-p
       a o1 res keys res1 length)))))

(defun uqvc-initial-state-p (a res keys)
  (and
   (<= 0 0)
   (uqvc-prefix-map-equivalent-p a 0 keys)
   (uqvc-prefix-list-equivalent-p a 0 res 0)
   (uqvc-unique-prefix-p res 0)))

(defun uqvc-nonnegative-loop-p (a res keys o1)
  (implies
   (<= 0 (+ o1 1))
   (and
    (uqvc-initial-state-p a res keys)
    (uqvc-all-loop-states-p a o1 res))))

(defun uqvc-negative-loop-p (a res o1)
  (implies
   (< (+ o1 1) 0)
   (and
    (<= 0 0)
    (<= 0 0)
    (<= (+ 0 0) (len res))
    (uqvc-all-results-p a res 0))))

(defun uqvc-res-obligation-p (a keys res)
  (let* ((length (len a))
         (o1 (- length 1)))
    (and
     (uqvc-nonnegative-loop-p
      a res keys o1)
     (uqvc-negative-loop-p
      a res o1))))

(defun-sk uqvc-all-result-buffers-p (a keys)
  (forall (res)
    (implies
     (uqvc-integer-list-p res)
     (implies
      (and
       (uqvc-zero-initialized-p res (len a))
       (equal (len res) (len a)))
      (uqvc-res-obligation-p a keys res)))))

(defun uqvc-map-obligation-p (a keys)
  (implies
   (equal keys nil)
   (and
    (<= 0 (len a))
    (uqvc-all-result-buffers-p a keys))))

(defun-sk uqvc-all-empty-maps-p (a)
  (forall (keys)
    (implies
     (uqvc-map-p keys)
     (uqvc-map-obligation-p a keys))))

(defun
  ntp4vc-pearl-hillel-challenge-unique-uniqueqtvc-statement
  (a)
  (implies
   (uqvc-integer-list-p a)
   (uqvc-all-empty-maps-p a)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
