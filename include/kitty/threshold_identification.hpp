/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <bitset>
#include <string>
#include <algorithm>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "properties.hpp"
#include "dynamic_truth_table.hpp"
#include "static_truth_table.hpp"
namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_neg_unate( const TT& tt )
{
  auto numvars = tt.num_vars();

  for ( auto i = 0u; i < numvars; i++ )
  {
    auto const tt1 = cofactor0( tt, i );
    auto const tt2 = cofactor1( tt, i );
    for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
    {
      if ( get_bit( tt1, bit ) >= get_bit( tt2, bit ) )
      {
        continue;
      }
      else
      {
        return false;
      }
    }
  }
  return true;
}



template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>


bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
TT ttu=tt;
std::vector<bool>inverted_variables(ttu.num_vars(),false);

  /* if tt is non-TF: */
  if ( !is_monotone(ttu) )
  {

    auto numvars = ttu.num_vars();

    for ( auto i = 0u; i < numvars; i++ )
    {
      auto const tt1 = cofactor0( ttu, i );
      auto const tt2 = cofactor1( ttu, i );
      bool neg_unate=false,eequal=false,pos_unate=false, change =false;

      for ( auto bit = 1; bit < ( 2 << ( numvars - 1 ) ); bit++ )
      {
        if ( get_bit( tt1, bit ) > get_bit( tt2, bit ) )
        {neg_unate=true;}
        if ( get_bit( tt1, bit ) < get_bit( tt2, bit ) )
        {pos_unate=true;}
        if ( get_bit( tt1, bit ) == get_bit( tt2, bit ) )
        {eequal=true;}

        }
        if (neg_unate && pos_unate) {return false;}
        if (neg_unate){
          inverted_variables.at(i)=true;
          for (uint64_t bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit=bit+2*pow(2,i)){
            std::vector<bool> tmp,tmp1;
            for(uint64_t k=bit; k<bit+pow(2,i);k++){
                tmp.push_back(get_bit(ttu,k));
          }
            std::reverse(tmp.begin(),tmp.end());
            for(uint64_t j=bit+pow(2,i); j<bit+2*pow(2,i);j++){
              //bool bittt,bittmp;
              //bittt=get_bit(ttu,j);
              //bittmp=tmp.at(tmp.size()-1);
              tmp1.push_back(get_bit(ttu,j));
              if (get_bit(ttu,j)!=tmp.at(tmp.size()-1)){
                flip_bit(ttu,j);
              }
              tmp.pop_back();
            }
            std::reverse(tmp1.begin(),tmp1.end());
            for(uint64_t j=bit; j<bit+pow(2,i);j++){
              //bool bittt,bittmp;
              //bittt=get_bit(ttu,j);
              //bittmp=tmp.at(tmp.size()-1);

              if (get_bit(ttu,j)!=tmp1.at(tmp1.size()-1)){
                flip_bit(ttu,j);
              }
              tmp1.pop_back();
            }

        }
      }
    }

    //return false;
  }


    lprec *lp;
    int  *colno = NULL, j,res, ret = 0;
    uint64_t Nrow;
    REAL *row = NULL;

    /* We will build the model row by row
       So we start with creating a model with 0 rows and 2 columns */
    const uint64_t Ncol = ttu.num_vars()+1; /* there are two variables in the model */
    Nrow = pow(2,ttu.num_vars());
    lp = make_lp(0, Ncol);
    if(lp == NULL)
      ret = 1; /* couldn't construct a new model... */

    if(ret == 0) {

      /* create space large enough for one row */
      colno = (int *) malloc(Ncol * sizeof(*colno));
      row = (REAL *) malloc(Ncol * sizeof(*row));
      if((colno == NULL) || (row == NULL))
        ret = 2;
    }

    if(ret == 0) {
      set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */
      for ( uint64_t index = 0; index < Nrow; index++ )
      {
        /* construct first row (120 x + 210 y <= 15000) */
        j = 0;
        std::bitset<64> bs(index);
        for ( uint64_t var = 1; var <= Ncol-1; var++ )
        {
          if (!inverted_variables.at(var-1))
          {
            /* k column */
            colno[j] = var;
            if ( bs.test( var - 1 ) )
            {
              row[j++] = 1;
            }
            else
            {
              row[j++] = 0;
            }
          }
          else{

            /* k column */
            colno[j] = var;
            if ( bs.test( var - 1 ) )
            {
              row[j++] = 1;
            }
            else
            {
              row[j++] = 0;
            }

          }
        }
        // T column
        colno[j] = Ncol; /* last column */
        row[j++] = -1;


        if (get_bit(ttu,index)){

          /* add the row to lpsolve */
          if(!add_constraintex(lp, j, row, colno, GE, 0))
            ret = 3;
        }
        else{

          /* add the row to lpsolve */
          if(!add_constraintex(lp, j, row, colno, LE, -1))
            ret = 3;

        }

      }



    }


    if(ret == 0) {
      set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */

      /* set the objective function (143 x + 60 y) */
      j = 0;
      for ( uint64_t var = 1; var <= Ncol; var++ )
      {
        colno[j] = var; /* first column */
        row[j++] = 1;
      }


      /* set the objective in lpsolve */
      if(!set_obj_fnex(lp, j, row, colno))
        ret = 4;
    }

    for ( uint64_t var = 1; var <= Ncol; var++ )
    {
      set_int(lp, var, TRUE); /* sets variable var to integer */
    }

    if(ret == 0) {
      /* set the object direction to minimize */
      set_minim(lp);

      /* just out of curiosity, now show the model in lp format on screen */
      /* this only works if this is a console application. If not, use write_lp and a filename */
      write_LP(lp, stdout);
      /* write_lp(lp, "model.lp"); */

      /* I only want to see important messages on screen while solving */
      set_verbose(lp, IMPORTANT);

      /* Now let lpsolve calculate a solution */
      ret = solve(lp);

      res=ret;



      if(ret == OPTIMAL)
        ret = 0;
      else
        ret = 5;
    }

    if(ret == 0) {
      /* a solution is calculated, now lets get some results */


      /* objective value */
      //printf("Objective value: %f\n", get_objective(lp));

      /* variable values */
      get_variables(lp, row);
      for(j = 0; j < Ncol; j++)
      {
        //printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
        linear_form.push_back(row[j]);
      }

      /* we are done now */
    }

    /* free allocated memory */
    if(row != NULL)
      free(row);
    if(colno != NULL)
      free(colno);

    if(lp != NULL) {
      /* clean up such that all used memory by lpsolve is freed */
      delete_lp(lp);
    }

 auto ss=inverted_variables.size();
  for ( uint64_t var = 0; var <inverted_variables.size(); var++ )
  {
    if (inverted_variables.at(var))
    {
      linear_form.at(inverted_variables.size())=linear_form.at(inverted_variables.size())-linear_form.at(var);
      linear_form.at(var)=-linear_form.at(var);

    }
  }



    /* if tt is TF: */
    /* push the weight and threshold values into `linear_form` */

  if ( res==0 )
  {
    *plf = linear_form;
    return true;
  }
  else{
    return false;
  }

}



std::string int_to_binary_string(uint64_t i){
  std::string s;
  while(! i==0) {s=(i%2==0 ?"0":"1")+s; i/=2;}
  return s;
}

std::vector<uint64_t> variables(const uint64_t& variable_number, const uint64_t& index){

  dynamic_truth_table variable_tt;
  //=create<dynamic_truth_table>(variable_number);
  create_from_binary_string(variable_tt,int_to_binary_string(index));
  std::vector<uint64_t> variables;

  for(int i=0; i<pow(2,variable_number);i++){

    variables.push_back(get_bit(variable_tt,i));
  }
}



} /* namespace kitty */
