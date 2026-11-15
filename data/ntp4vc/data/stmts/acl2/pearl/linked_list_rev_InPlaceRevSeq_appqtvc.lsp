;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/linked_list_rev_InPlaceRevSeq_appqtvc: the linked-list append
;; verification condition, preserving disjoint list segments and the loop
;; transition used to splice the second list onto the first. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source location type is abstract and inhabited.  Its potentially
;; infinite carrier, distinguished null location, and arbitrary successor
;; function are represented conservatively; the source function typing is an
;; explicit assumption of the statement.

(defstub llr-loc-p (x) t)
(defstub llr-null () t)
(defstub llr-next (x) t)

(defun-sk llr-next-closed-p ()
  (forall (x)
    (implies
     (llr-loc-p x)
     (llr-loc-p (llr-next x)))))

(defun llr-location-interface-p ()
  (and
   (llr-loc-p (llr-null))
   (llr-next-closed-p)))

(defun llr-loc-list-p (xs)
  (if (consp xs)
      (and
       (llr-loc-p (car xs))
       (llr-loc-list-p (cdr xs)))
    (equal xs nil)))

;; This Boolean equality is definitionally the source EQ_LOC satisfying
;; eq_loc l1 l2 = true iff l1 = l2.

(defun llr-eq-loc (left right)
  (equal left right))

;; NFIX is Int.toNat on integer arguments: negative integers map to zero and
;; nonnegative integers retain their value.

(defun llr-nth-i (index xs)
  (nth (nfix index) xs))

(defun llr-drop-i (count xs)
  (nthcdr (nfix count) xs))

;; Pointwise disjointness keeps both source integer-index quantifiers and their
;; bounds.  The list predicates at every use site provide the source typing.

(defun-sk llr-disjoint-p (left right)
  (forall (i1 i2)
    (implies
     (and
      (integerp i1)
      (<= 0 i1)
      (< i1 (len left))
      (integerp i2)
      (<= 0 i2)
      (< i2 (len right)))
     (not
      (equal
       (llr-nth-i i1 left)
       (llr-nth-i i2 right))))))

(defun-sk llr-all-nonnull-p (xs)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (len xs)))
     (not
      (equal
       (llr-nth-i i xs)
       (llr-null))))))

(defun-sk llr-all-links-p (xs)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (- (len xs) 1)))
     (equal
      (llr-next (llr-nth-i i xs))
      (llr-nth-i (+ i 1) xs)))))

(defun llr-list-seg-p (start xs finish)
  (let ((n (len xs)))
    (and
     (llr-all-nonnull-p xs)
     (or
      (and
       (equal start finish)
       (equal n 0))
      (and
       (<= 1 n)
       (equal (llr-nth-i 0 xs) start)
       (equal
        (llr-next (llr-nth-i (- n 1) xs))
        finish)
       (llr-all-links-p xs))))))

;; Function.update next p l2 is represented extensionally by this selector.

(defun llr-updated-next (x update-point update-value)
  (if (equal x update-point)
      update-value
    (llr-next x)))

(defun-sk llr-all-updated-links-p
    (xs update-point update-value)
  (forall (i)
    (implies
     (and
      (integerp i)
      (<= 0 i)
      (< i (- (len xs) 1)))
     (equal
      (llr-updated-next
       (llr-nth-i i xs)
       update-point
       update-value)
      (llr-nth-i (+ i 1) xs)))))

(defun llr-updated-list-seg-p
    (start xs finish update-point update-value)
  (let ((n (len xs)))
    (and
     (llr-all-nonnull-p xs)
     (or
      (and
       (equal start finish)
       (equal n 0))
      (and
       (<= 1 n)
       (equal (llr-nth-i 0 xs) start)
       (equal
        (llr-updated-next
         (llr-nth-i (- n 1) xs)
         update-point
         update-value)
        finish)
       (llr-all-updated-links-p
        xs update-point update-value))))))

;; These two universal predicates are the pointwise characterizations of the
;; one-element construction O7 and append construction O8 in the source VC.

(defun-sk llr-cons-tail-description-p (o6 o7)
  (forall (i)
    (implies
     (and
      (integerp i)
      (< 0 i)
      (<= i (len o6)))
     (equal
      (llr-nth-i i o7)
      (llr-nth-i (- i 1) o6)))))

(defun-sk llr-append-index-description-p (left right output)
  (forall (i)
    (and
     (implies
      (and
       (integerp i)
       (<= 0 i)
       (< i (len left)))
      (equal
       (llr-nth-i i output)
       (llr-nth-i i left)))
     (implies
      (and
       (integerp i)
       (<= (len left) i)
       (< i (len output)))
      (equal
       (llr-nth-i i output)
       (llr-nth-i (- i (len left)) right))))))

(defun llr-nonnull-successor-branch-p
    (l1 l1m l1pm pm p)
  (and
   (and
    (<= 0 1)
    (<= 1 (len pm)))
   (let* ((o6 nil)
          (o7 (cons p o6)))
     (implies
      (and
       (equal (len o7) (+ 1 (len o6)))
       (equal (llr-nth-i 0 o7) p)
       (llr-cons-tail-description-p o6 o7))
      (let ((o8 (append l1pm o7)))
        (implies
         (and
          (equal
           (len o8)
           (+ (len l1pm) (len o7)))
          (llr-append-index-description-p
           l1pm o7 o8))
         (let ((tail (llr-drop-i 1 pm)))
           (and
            (not (equal p (llr-null)))
            (and
             (<= 0 (len pm))
             (< (len tail) (len pm)))
            (not
             (equal (llr-next p) (llr-null)))
            (llr-list-seg-p
             l1 o8 (llr-next p))
            (llr-list-seg-p
             (llr-next p) tail (llr-null))
            (equal
             (append o8 tail)
             l1m)
            (llr-disjoint-p o8 tail)))))))))

(defun llr-split-conclusion-p
    (l1 l1m l2 l2m l1pm pm p)
  (and
   (not (equal p (llr-null)))
   (let* ((o3 (llr-null))
          (o4 (llr-next p))
          (o5 (llr-eq-loc o4 o3)))
     (implies
      (iff
       (equal o5 t)
       (equal o4 o3))
      (if (not (equal o5 t))
          (llr-nonnull-successor-branch-p
           l1 l1m l1pm pm p)
        (and
         (not (equal p (llr-null)))
         (llr-updated-list-seg-p
          l1
          (append l1m l2m)
          (llr-null)
          p
          l2)))))))

(defun-sk llr-all-splits-p (l1 l1m l2 l2m)
  (forall (l1pm pm p)
    (implies
     (and
      (llr-loc-list-p l1pm)
      (llr-loc-list-p pm)
      (llr-loc-p p)
      (not (equal p (llr-null)))
      (llr-list-seg-p l1 l1pm p)
      (llr-list-seg-p p pm (llr-null))
      (equal (append l1pm pm) l1m)
      (llr-disjoint-p l1pm pm))
     (llr-split-conclusion-p
      l1 l1m l2 l2m l1pm pm p))))

(defun llr-app-vc-conclusion-p (l1 l1m l2 l2m)
  (let* ((o1 (llr-null))
         (o2 (llr-eq-loc l1 o1)))
    (implies
     (iff
      (equal o2 t)
      (equal l1 o1))
     (if (equal o2 t)
         (llr-list-seg-p
          l2
          (append l1m l2m)
          (llr-null))
       (and
        (and
         (not (equal l1 (llr-null)))
         (llr-list-seg-p l1 nil l1)
         (llr-list-seg-p
          l1 l1m (llr-null))
         (equal (append nil l1m) l1m)
         (llr-disjoint-p nil l1m))
        (llr-all-splits-p l1 l1m l2 l2m))))))

(defun
    ntp4vc-pearl-linked-list-rev-inplacerevseq-appqtvc-statement
    (l1 l1m l2 l2m)
  (implies
   (and
    (llr-location-interface-p)
    (llr-loc-p l1)
    (llr-loc-list-p l1m)
    (llr-loc-p l2)
    (llr-loc-list-p l2m)
    (llr-list-seg-p
     l1 l1m (llr-null))
    (llr-list-seg-p
     l2 l2m (llr-null))
    (llr-disjoint-p l1m l2m))
   (llr-app-vc-conclusion-p
    l1 l1m l2 l2m)))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
