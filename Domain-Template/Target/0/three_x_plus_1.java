int sum  = 0;
   	   int sum2 = 0;
   	   {
   			 int x;
   			 int i;
   			 for (i = 1; i < 32; i++) {
   				 x = i;
   				 while (x != 1) {
   					 int j;
   					 for (j = 1; j < 3; j++) {
   						 if (x % 2 == 0) {
   							 x = x / 2;
   						 }
   						 if (x % 2 != 0) {
   							 x = 3*x + 1;
   						 }
   					 }
   					 sum = sum + 3;
   				 }
   			 }
   	 }

   	 
   	 {
   		 int sum1 = 0;
   		 int x;
   		 int i;
   		 for (i = 15; i > 1; --i) {
   			 x = i;
   			 while (x != 1) {
   				 int j;
   				 for (j = 1; j < 3; ++j){
   					 if (x % 2 == 0) {
   						 x = x / 2;
   					 }
   					 if (x % 2 != 0) {
   						 x = 3*x + 1;
   					 }
   				 }
   				 sum1 = sum1 + 3;
   			 }
   		 }
   		 print sum1;
   	 }
   	 
   	 {
   		 int x;
   		 int i;
   		 for (i = -24; i < -1; ++i) {
   			 x = i;
   			 while (x != 1) {
   				 int j;
   				 for (j = 1; j < 3; ++j){
   					 if (x % 2 == 0) {
   						 x = |x/2|;
   					 }
   					 if (x % 2 != 0) {     
   						 x = |3*x| + 1;
   					 }
   				 }
   				 sum2 = ((sum2 + 3));
   			 }
   		 }
   		 print sum2;
   	 }
   	 print sum;


   	 if (sum2 == 423 && !(sum != 888)) {
  		 if (sum2 + 465 >= sum && sum <= sum2 + 465) {
   			 if (2 ^ 0 < 2 && 2 ^ 1 > 2 || 2 ^ 3 < 8) {
   				 print 1;
   			 }
   			 if (!(2 ^ 0 < 2 && 2 ^ 1 > 2 || 2 ^ 3 < 8)) {
   				 print 2;
   			 }
   		 if (!(sum2 + 465 >= sum && sum <= sum2 + 465)) {
   			 print 3;
   		 }
   	 }
   	 if (!(sum2 == 423 && !(sum != 888))) {
   		 print 4;
   	 }
    }
