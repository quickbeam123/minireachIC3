/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     CLOCK                              * */
/* *                                                        * */
/* *  $Module:   CLOCK                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1999, 2001                  * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the FreeBSD    * */
/* *  Licence.                                              * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the LICENCE file       * */ 
/* *  for more details.                                     * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 1.6 $                                         * */
/* $State: Exp $                                            * */
/* $Date: 2011-05-22 11:47:56 $                             * */
/* $Author: weidenb $                                       * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: spass@mpi-inf.mpg.de                * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

/* $RCSfile: clock.h,v $ */

#ifndef _CLOCK_
#define _CLOCK_

#include <inttypes.h>
#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>

typedef enum {
  clock_OVERALL,
  clock_PARSE,
  clock_SIMP,
  clock_MAIN,
  clock_SOLVER_EXTEND,
  clock_SOLVER_PUSH,
  clock_TYPESIZE
} CLOCK_CLOCKS;


typedef struct timeval CLOCK_TMS;

void   clock_Init(void);
void   clock_InitCounter(CLOCK_CLOCKS);
void   clock_StartCounter(CLOCK_CLOCKS);
void   clock_StopPassedTime(CLOCK_CLOCKS);
void   clock_StopAddPassedTime(CLOCK_CLOCKS);
double clock_GetSeconds(CLOCK_CLOCKS);
double clock_GetAkku(CLOCK_CLOCKS);
void   clock_PrintTime(CLOCK_CLOCKS);

#endif
