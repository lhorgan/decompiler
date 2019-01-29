; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
#|(defun tau-listp (tl)
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp (first tl)) (tau-listp (rest tl))))
        )
  )|#

#|(defmacro tau-listp (tl)
  (list 'cond (list (list 'integerp tl) T)
              (list (list 'endp tl) T)
              (list (list 'listp tl) (list 'and (list 'tau-listp (list 'first tl)) (list 'tau-listp (list 'rest tl))))))|#

#|(skip-proofs
(defunc tau-listp2 (tl)
  :input-contract (or (integerp tl) (true-listp tl))
  :output-contract (booleanp (tau-listp2 tl))
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp2 (first tl)) (tau-listp2 (rest tl))))
        )
  )
)|#

;(skip-proofs
(defunc tau-listp (tl)
  :input-contract T
  :output-contract (booleanp (tau-listp tl))
  #|(cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp (first tl)) (tau-listp (rest tl))))
        (T nil)
        )|#
  (integer-listp tl)
  )
;)

(defthm sillyme
  (implies (integer-listp tl)
           (tau-listp tl)))

#|(defthm typing
  (implies (tau-listp x) (or (true-listp x) (integerp x)))
  )|#

(defmacro lenp (delta n)
  (list 'and (list 'natp n) (list 'true-listp delta) (list '>= (list 'len delta) n))
  )

(defunc i_return (delta)
   :input-contract (and (true-listp delta) (tau-listp delta) (integerp (first delta)))
   :output-contract (integerp (first delta))
   (first delta)
   )

#|(defunc taup (a)
  :input-contract a
  :output-contract (booleanp (taup a))
  (or (natp a) (listp a))
  )|#


(defunc i_dup (delta)
  :input-contract (and (tau-listp delta)
                       (true-listp delta)
                       (lenp delta 1))
  :output-contract (tau-listp (i_dup delta))
  (cons (first delta) delta)
  )

(defunc i_const (n delta)
  :input-contract (and 
                   (tau-listp delta) 
                   (true-listp delta) 
                   (integerp n))
  :output-contract (tau-listp (i_const n delta))
  (cons n delta)
  )

(defmacro if_zero (delta a f1 f2)
  (list 'cons (list 'if (list 'equal a 0) f1 f2) delta)
  )


(defmacro goto (delta f)
  (list f delta)
  )

(defunc i_pop (delta)
  :input-contract (and (true-listp delta) (tau-listp delta) (lenp delta 1))
  :output-contract (and (true-listp (i_pop delta)) (tau-listp delta))
  (rest delta)
  )

(defunc i_add (delta)
  :input-contract (and (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (true-listp (i_add delta)) (integerp (first (i_add delta))))
  (cons (+ (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_swap (delta)
  :input-contract (and (tau-listp delta) (lenp delta 2))
  :output-contract (and (tau-listp (i_swap delta)) (true-listp delta))
  (cons (second delta) (cons (first delta) (rest (rest delta))))
  )

(defthm nil-if-pop-twice-from-list-of-two
  (implies (and (true-listp x) (tau-listp x) (equal (len x) 2)) (equal (i_pop (i_pop x)) nil))
  )

(defunc i_mul (delta)
  :input-contract (and 
                   (true-listp delta) 
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   )
  :output-contract (and
                    (true-listp (i_mul delta))
                    (tau-listp (i_mul delta))
                    (integerp (first (i_mul delta))))
  :function-contract-hints (nil-if-pop-twice-from-list-of-two)
  (cons (* (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_div (delta)
  :input-contract (and 
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_div delta))
                    (tau-listp (i_div delta))
                    (integerp (first (i_div delta))))
  (cons (floor (/ (first delta) (second delta)) 1) (i_pop (i_pop delta)))
  )

(defunc i_mod (delta)
  :input-contract (and 
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_mod delta))
                    (tau-listp (i_mod delta))
                    (integerp (first (i_mod delta))))
  (cons (mod (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc is_a_list (list)
  :input-contract (true-listp list)
  :output-contract (booleanp (is_a_list list))
  (cond ((equal list nil) T)
        ((and (true-listp (first list)) #|(atom-listp (first list))|# (equal (len (first list)) 2) (is_a_list (rest list))) T)
        (T nil))
  )

(defunc i_store (delta mu)
  :input-contract (and
                   (true-listp delta)
                   (lenp delta 2)
                   (tau-listp delta)
                   (integerp (first delta))
                   (true-listp mu)
                   (is_a_list mu)
                   )
  :output-contract (and
                    ;(equal (first delta) (first (first (second (i_store delta mu)))))
                    ;(equal (second delta) (second (first (second (i_store delta mu)))))
                    ;(equal (len (first (i_store delta mu))) (- (len delta) 2))
                    (is_a_list (second (i_store delta mu)))
                    (tau-listp (first (i_store delta mu)))
                    )
  (list (i_pop (i_pop delta)) 
        (cons (list (first delta) (second delta)) mu))
  )
  
(defunc get_val (mu key)
  :input-contract (and (true-listp mu)  (is_a_list mu) (integerp key))
  :output-contract (atom key)
  (cond ((equal mu nil) nil)
        ((equal (first (first mu)) key) (second (first mu)))
        (T (get_val (rest mu) key))
        )
  )

(defunc i_load (delta mu)
  :input-contract (and
                   (lenp mu 1)
                   (true-listp mu)
                   (is_a_list mu)
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 1)
                   (integerp (first delta))
                   )
  :output-contract (true-listp (i_load delta mu))
  (let ((val (get_val mu (first delta))))
  (append (if (true-listp val) val (list val)) (i_pop delta)))
  )

(defunc i_lt (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (< (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc i_gt (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (> (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc i_equal (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (equal (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc tau-boolp (num)
  :input-contract (integerp num)
  :output-contract (booleanp (tau-boolp num))
  (or (= num 1) (= num 0))
  )

#| we don't need BYTES in the BODY of the function
but ACL2 complains if we don't have it, so we
cons it and then ignore it |#
(defunc i_push (bytes val delta)
  :input-contract (and (integerp val)
                       (integerp bytes)
                       (>= bytes 1) 
                       (<= bytes 32) 
                       (>= val 0) 
                       (< val (expt 2 bytes))
                       (true-listp delta)
                       (tau-listp delta))
  :output-contract (tau-listp (i_push bytes val delta))
  #|(declare (ignore bytes))|#
  (cons val (rest (cons bytes delta)))
  )

(defunc fetch (delta ind)
  :input-contract (and (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (true-listp delta)
                       (tau-listp delta)
                       (lenp delta ind))
  :output-contract (integerp (fetch delta ind))
  (if (equal ind 1) (first delta) (fetch (rest delta) (- ind 1)))
  )

(defunc i_dup_* (ind delta)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (lenp delta ind))
  :output-contract (tau-listp (i_dup_* ind delta))
  (cons (fetch delta ind) delta)
  )

(defthm rest_tau
  (implies (and (true-listp delta)
                (tau-listp x)
                (>= (len x) 1))
           (tau-listp (rest x)))
  )

(defthm grk
  (implies (and (true-listp x) (>= (len x) 1)) (true-listp (rest x)))
  )#|ACL2s-ToDo-Line|#


(defunc i_swap_* (ind delta)
  :input-contract (and (integer-listp delta)
                       (natp ind)
                       (>= ind 0)
                       (<= ind 16)
                       (lenp delta (+ 2 ind)))
  :output-contract (integer-listp (i_swap_* ind delta))
  (append
   (cons (nth (+ ind 1) delta) (subseq delta 1 (+ ind 1)))
   (cons (first delta)
             (if (< (len delta) (+ ind 2)) nil (subseq delta (+ ind 2) (len delta)))
             ))
  )