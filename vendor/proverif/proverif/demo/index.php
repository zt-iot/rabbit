<?php
// <!-- --------------  START HEADER ------------------->

echo "
<!DOCTYPE html>
<html lang=\"en\">
<head lang=\"en\">
    <meta charset=\"utf-8\">
    <meta http-equiv=\"X-UA-Compatible\" content=\"IE=edge\">
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">

    <base href=\"http://proverif24.paris.inria.fr/\">

    <link rel=\"icon\" type=\"image/png\" href=\"https://proverif.inria.fr/favicon.png\">
    <link href=\"https://proverif.inria.fr/css/bootstrap.min.css\" rel=\"stylesheet\">
    <link rel=\"stylesheet\" href=\"./css/styles.css?v=18\">

    <title>ProVerif demo</title>
    <meta name=\"description\" content=\"Automated Symbolic Protocol Verification\">
    <script type=\"application/ld+json\">
        {
            \"@context\": \"https://schema.org\",
            \"@type\": \"SoftwareApplication\",
            \"name\": \"ProVerif\",
            \"description\": \"ProVerif is an automatic symbolic protocol verifier which proves security properties of cryptographic protocols.\",
            \"applicationCategory\": \"Security, Cryptography\",
            \"programmingLanguage\": \"OCaml\",
            \"downloadUrl\": \"https://bblanche.gitlabpages.inria.fr/proverif/\",
            \"softwareHelp\": {
                \"@type\": \"CreativeWork\",
                \"url\": \"https://bblanche.gitlabpages.inria.fr/proverif/manual.pdf\"
            }
        }
    </script>
</head>
<body>

<nav class=\"navbar sticky-top navbar-expand-lg bg-dark border-bottom border-body\" data-bs-theme=\"dark\">
    <div class=\"container-fluid container-narrow\">
        <button class=\"navbar-toggler\" type=\"button\" data-bs-toggle=\"collapse\"
                data-bs-target=\"#navbarSupportedContent\" aria-controls=\"navbarSupportedContent\"
                aria-expanded=\"false\" aria-label=\"Toggle navigation\">
            <span class=\"navbar-toggler-icon\"></span>
        </button>
        <div class=\"collapse navbar-collapse\" id=\"navbarSupportedContent\">
            <ul class=\"navbar-nav mb-2 mb-lg-0\">
                <li class=\"nav-item\">
                    <a class=\"nav-link\" aria-current=\"page\" href=\"https://proverif.inria.fr/\">ProVerif</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/install.html\">Install</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/usage.html\">Usage</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link active\" href=\"./\">Demo</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/manual.pdf\">Manual</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/25years.html\">25 years workshop</a>
                </li>
            </ul>
            <ul class=\"navbar-nav ms-auto mb-2 mb-lg-0\">
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/users.html\">Users</a>
                </li>
                <li class=\"nav-item\">
                    <a class=\"nav-link\" href=\"https://proverif.inria.fr/publications.html\">Publications</a>
                </li>
            </ul>
        </div>
    </div>
</nav>

<section class=\"abstract\">
    <div class=\"container-narrow\">

<H1>Online Demo for ProVerif</H1>

<p class=\"subtitle\">
Proverif in OCaml by Bruno Blanchet, Vincent Cheval and Marc Sylvestre<br>
Web interface by Sreekanth Malladi and Bruno Blanchet
</p>

<form action=\"".$_SERVER['PHP_SELF']."\" method=\"post\">
";

// <!-- -------------  END HEADER -------------------------->

// ---------------    INITIALIZE VARIABLES ----------------

// delete old files if there is less than 5GB left
global $CLEANUP_SPACE; $CLEANUP_SPACE = 5000000000; 

// don't run an analysis if there is less than 4.5GB left
// we must have $REQUIRED_SPACE <= $CLEANUP_SPACE
global $REQUIRED_SPACE; $REQUIRED_SPACE = 4500000000; 

// delay during which the files are guaranteed to be kept, in seconds.
global $DELAY; $DELAY = 1800; 

// maximal delay during which files are kept, in seconds (50 days)
global $MAXDELAY; $MAXDELAY = 4320000;

// maximum number of active ProVerif processes
global $MAX_PROC; $MAX_PROC = 15;

$protocol = $_POST['inpProtTA'];
$protSelected = $_POST['protSel'];
$loadProtPressed = $_POST['loadProtBtn'];
$analPressed = $_POST['analBtn'];

$protocol = stripslashes( $protocol );

if( $protSelected != "" ) // user made a selection
{
	// Open the selected file in ./protocols folder
	$inpFHand = fopen("./examples/".$protSelected, "r");
	
	// Update $input variable
	$protocol = "";
	while( !feof($inpFHand) )
		$protocol = $protocol.fgets( $inpFHand );
	fclose( $inpFHand );

}

// ------------- END INITIALIZE VARIABLES ----------------


// -------------- START FIRST ROW OF TABLE ----------------

print "<table align=center>";

print "<tr>";  // Print first row (protocol list, load button, input TA).
print <<<HERE
<td valign=top>
<b>Input: Select protocol  </b>
<P>
<select size=10 name=protSel class="small">
       <option value = "secr-auth/NeedhamSchroederPK.pv">Needham-Schroeder public key</option>
       <option value = "secr-auth/NeedhamSchroederPK-corr.pv">Needham-Schroeder-Lowe</option>
       <option value = "secr-auth/WooLamSK-GJ01.pv">Woo-Lam shared key (variant by Gordon, Jeffrey)</option>
       <option value = "secr-auth/WooLamSK-corr-GJ01.pv">Woo-Lam shared key corrected</option>
       <option value = "secr-auth/SimplerYahalom.pv">Simpler Yahalom bidirectional</option>
       <option value = "secr-auth/ssh-transport.pv">SSH Transport</option>
       <option value = "noninterf/OtwayRees.pv">Otway-Rees (strong secrecy)</option>
       <option value = "weaksecr/vote.pv">naive voting protocol (guessing attack)</option>
       <option value = "weaksecr/EKE.pv">EKE (no guessing attack)</option>
       <option value = "weaksecr/AugmentedEKE2.pv">Augmented EKE (no guessing attack)</option>
       <option value = "weaksecr/SignedAugmentedEKE1.pv">Signed augmented EKE (no guessing attack)</option>
       <option value = "choice/macs.pv">Comparison of MAC schemes</option>
       <option value = "choice/proba-pk.pv">Probabilistic public-key encryption</option>
       <option value = "ffgg/ffgg10.pv">ffgg 10</option>
       <option value = "lemma/toy-one-dec.pv">Example with [precise]</option>
       <option value = "lemma/yubikey-less-axioms.pv">Yubikey (example with axiom and lemma)</option>
       <option value = "lemma/secure-device.pv">Secure device (example with axiom)</option>
</select>
</td>
HERE;

print "<td valign=top><b>or enter your protocol below:</b>
<P>
<textarea name=\"inpProtTA\" rows=\"10\" cols=\"75\" class=\"small\">".$protocol."</textarea></td>";

print "</tr>";


// -------------  END FIRST ROW; START SECOND ROW ------------------


print "<tr>";
print "<td align=left><input type=\"submit\" name=\"loadProtBtn\" value=\"Load Protocol\"></td>";

print "<td align=left><input type=\"submit\" name=\"analBtn\" value=\"Verify\"></td>";

print "</tr></table></form>";

// ------------  END SECOND ROW, START THIRD ROW  -------------

if( $analPressed == "Verify" )
{
	analyze( $protocol );
}


// ------------  END THIRD ROW, START FOOTER   ---------------
echo "<P>
Please do <b>not</b> reload the page while waiting for ProVerif to complete.
That would launch the same example from the start again.
<P>
Each process is limited to 1 Gb RAM and 100 seconds CPU time.
Moreover, there is no security mechanism to protect the confidentiality of
your data, so you should not enter confidential data in this form.
If you want to verify an example that requires more resources or 
a confidential protocol, please download and install
your own copy of ProVerif.
    </div>
</section>


<script src=\"https://proverif.inria.fr/js/bootstrap.bundle.min.js\"></script>
<script src=\"https://proverif.inria.fr/js/main.js\"></script>

</body>
</html>";

// ----------       END FOOTER       -------------------------

 // The main function to analyze protocols (first save input protocol, 
 // then prepare input.pl and
 // finally execute expression pl < input.pl 
 function analyze( $protocol )
 {
        global $REQUIRED_SPACE, $CLEANUP_SPACE, $DELAY, $MAXDELAY, $MAX_PROC;

	if($protocol == "")
	{
		print "<P><font size=6 color=red><b>Warning:</b> Select or 
		enter a protocol!</font>";
		return;
	}


   // determine the session number

   // remove files older than $MAXDELAY
   $dir = scandir("./tmpfiles");
   $size = sizeof($dir);
   $current_time = time();		
   for ($i = 0; $i < $size; ++$i)
   {
      $cur_dir = $dir[$i];
      if (is_numeric($cur_dir)) {
         if (filemtime("./tmpfiles/".$cur_dir) < $current_time - $MAXDELAY) {
           // session too old, delete it
           exec("rm -rf ./tmpfiles/".$cur_dir);
         }
      }
   }

   if (disk_free_space(".") < $CLEANUP_SPACE) {
     // not too much free space, do some more cleanup (remove files older than $DELAY)
     $dir = scandir("./tmpfiles");
     $size = sizeof($dir);
     $current_time = time();		
     for ($i = 0; $i < $size; ++$i)
     {
        $cur_dir = $dir[$i];
        if (is_numeric($cur_dir)) {
           if (filemtime("./tmpfiles/".$cur_dir) < $current_time - $DELAY) {
             // session too old, delete it
             exec("rm -rf ./tmpfiles/".$cur_dir);
           }
        }
     }

     if (disk_free_space(".") < $REQUIRED_SPACE) {
         print "<P><font size=6 color=red><b>Error:</b> too many analyses started recently, no more free space to store your files. Please come back later. (Files can get deleted after 30 min.)</font>";
	 return;
     }
   }

   $SESSION_NUM = mt_rand(0, 99999999);
   $SESSION_STRING = str_pad($SESSION_NUM, 8, "0", STR_PAD_LEFT);
   $iter = 0;
   while (file_exists("./tmpfiles/".$SESSION_STRING) && ($iter < 10)) {
     $SESSION_NUM = mt_rand(0, 99999999);
     $SESSION_STRING = str_pad($SESSION_NUM, 8, "0", STR_PAD_LEFT);
     $iter++;
   }
   if (file_exists("./tmpfiles/".$SESSION_STRING)) {
         print "<P><font size=6 color=red><b>Error:</b> I don't manage to find a directory name that is not used, strange!</font>";
	 return;
   }

	// WRITE PROTOCOL ENTERED IN INPPROT TEXT AREA
	// TO A FILE, ./tmpfiles/$SESSION_STRING/inpProt

        if (!mkdir("./tmpfiles/".$SESSION_STRING)) {
	   echo "<P><font size=6 color=red><b>Error:</b> Directory creation failed, strange!</font>";
	   return;
	}
	exec("ps aux | grep proverif | grep -v ulimit > ./tmpfiles/".$SESSION_STRING."/activeprocesses");
	if (count(file("./tmpfiles/".$SESSION_STRING."/activeprocesses")) > $MAX_PROC) {
           echo "<P><font size=6 color=red><b>Error:</b> Too many ProVerif processes running. Please come back later.</font>";
	   return;
	}
	$inpFHand = fopen("./tmpfiles/".$SESSION_STRING."/inpProt.pv", "w");
	fputs( $inpFHand, $protocol );
	fclose( $inpFHand );

	$output = array();
	mkdir("./tmpfiles/".$SESSION_STRING."/html");
	exec("cp cssproverif.css ./tmpfiles/".$SESSION_STRING."/html");

        print "<P><A HREF=\"tmpfiles/".$SESSION_STRING."/html/index.html\"><b>ProVerif HTML output</b></A>
<P>
The HTML output is kept for at least 30 minutes. It is kept at most 50 days if there is enough free space. You can obviously save the web pages if you want to keep them.";
        print "<P><b>ProVerif text output:</b> 
	        <P>
                <textarea
                name=\"opTA\" value=\"ProVerif output here\" rows=\"20\"
                cols=\"125\">";

        system("ulimit -t 100; ulimit -f 50000; ulimit -m 1000000; ./bin/proverif -html ./tmpfiles/".$SESSION_STRING."/html ./tmpfiles/".$SESSION_STRING."/inpProt.pv", $status);

        print "</textarea>";
 }
?>
